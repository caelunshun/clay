use bumpalo::Bump;
use derive_where::derive_where;
use std::{
    cell::RefCell,
    fmt, mem,
    num::NonZeroU64,
    ops::Deref,
    ptr::NonNull,
    sync::atomic::{AtomicU64, Ordering::Relaxed},
};

// === GpArena === //

trait Anything {}

impl<T: ?Sized> Anything for T {}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct GpGeneration(NonZeroU64);

pub struct GpArena<'a> {
    generation: GpGeneration,
    bump: bumpalo::Bump,
    drop_queue: RefCell<DropQueue<'a>>,
}

struct DropQueue<'a> {
    singles: Vec<NonNull<dyn Anything + 'a>>,
    lists: Vec<DropQueueList>,
}

#[derive(Copy, Clone)]
struct DropQueueList {
    base: NonNull<()>,
    len: usize,
    drop: unsafe fn(NonNull<()>, usize),
}

impl fmt::Debug for GpArena<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GpArena").finish_non_exhaustive()
    }
}

impl Default for GpArena<'_> {
    fn default() -> Self {
        static ID_GEN: AtomicU64 = AtomicU64::new(1);

        let generation = GpGeneration(NonZeroU64::new(ID_GEN.fetch_add(1, Relaxed)).unwrap());

        Self {
            generation,
            bump: Bump::new(),
            drop_queue: RefCell::new(DropQueue {
                singles: Vec::new(),
                lists: Vec::new(),
            }),
        }
    }
}

impl<'l> GpArena<'l> {
    pub fn generation(&self) -> GpGeneration {
        self.generation
    }
}

impl Drop for GpArena<'_> {
    fn drop(&mut self) {
        let inner = self.drop_queue.get_mut();

        for &single in &inner.singles {
            unsafe { single.drop_in_place() };
        }

        for &DropQueueList { base, len, drop } in &inner.lists {
            unsafe { drop(base, len) };
        }
    }
}

// === GpMutPtr === //

#[derive_where(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[repr(C)]
pub struct GpMutPtr<T: ?Sized> {
    generation: GpGeneration,
    ptr: NonNull<T>,
}

impl<T: ?Sized> GpMutPtr<T> {
    pub fn new<'l>(value: T, arena: &GpArena<'l>) -> Self
    where
        T: Sized + 'l,
    {
        let ptr = NonNull::from(arena.bump.alloc(value));

        arena.drop_queue.borrow_mut().singles.push(ptr);

        Self {
            generation: arena.generation,
            ptr,
        }
    }

    pub unsafe fn new_unchecked(generation: GpGeneration, ptr: NonNull<T>) -> Self {
        Self { generation, ptr }
    }

    pub fn erase<V>(self, erase: fn(&Self) -> &V) -> GpErasedMutPtr<V>
    where
        T: Sized,
        V: ?Sized + GpAnyMutPtr,
    {
        GpErasedMutPtr::new(self, erase)
    }
}

impl<T> GpMutPtr<[T]> {
    pub fn new_slice<'l>(value: &[T], arena: &GpArena<'l>) -> Self
    where
        T: Clone + 'l,
    {
        let ptr = NonNull::from(arena.bump.alloc_slice_clone(value));

        arena.drop_queue.borrow_mut().lists.push(DropQueueList {
            base: ptr.cast(),
            len: ptr.len(),
            drop: |ptr, len| unsafe {
                NonNull::slice_from_raw_parts(ptr.cast::<T>(), len).drop_in_place();
            },
        });

        Self {
            generation: arena.generation,
            ptr,
        }
    }

    pub fn new_iter<'l>(
        value: impl IntoIterator<Item = T, IntoIter: ExactSizeIterator>,
        arena: &GpArena<'l>,
    ) -> Self
    where
        T: 'l,
    {
        let ptr = NonNull::from(arena.bump.alloc_slice_fill_iter(value));

        arena.drop_queue.borrow_mut().lists.push(DropQueueList {
            base: ptr.cast(),
            len: ptr.len(),
            drop: |ptr, len| unsafe {
                NonNull::slice_from_raw_parts(ptr.cast::<T>(), len).drop_in_place();
            },
        });

        Self {
            generation: arena.generation,
            ptr,
        }
    }
}

impl<T: ?Sized> GpMutPtr<T> {
    pub fn generation(self) -> GpGeneration {
        self.generation
    }

    pub fn ptr(self) -> NonNull<T> {
        self.ptr
    }

    pub fn r<'a>(self, arena: &'a GpArena<'_>) -> &'a T {
        assert_eq!(arena.generation, self.generation);

        unsafe { self.ptr.as_ref() }
    }

    pub fn m<'a>(mut self, arena: &'a mut GpArena<'_>) -> &'a mut T {
        assert_eq!(arena.generation, self.generation);

        unsafe { self.ptr.as_mut() }
    }
}

// === GpErasedMutPtr === //

#[derive_where(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct GpErasedMutPtr<T: ?Sized + GpAnyMutPtr> {
    ptr: GpMutPtr<()>,
    #[derive_where(skip)]
    erase: unsafe fn(&GpMutPtr<()>) -> &T,
}

impl<T: ?Sized + GpAnyMutPtr> GpErasedMutPtr<T> {
    pub fn new<V>(ptr: GpMutPtr<V>, erase: fn(&GpMutPtr<V>) -> &T) -> Self {
        Self {
            ptr: unsafe { GpMutPtr::new_unchecked(ptr.generation(), ptr.ptr().cast()) },
            erase: unsafe {
                mem::transmute::<fn(&GpMutPtr<V>) -> &T, unsafe fn(&GpMutPtr<()>) -> &T>(erase)
            },
        }
    }
}

impl<T: ?Sized + GpAnyMutPtr> Deref for GpErasedMutPtr<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { (self.erase)(&self.ptr) }
    }
}

mod sealed {
    pub trait Sealed {}
}

pub trait GpAnyMutPtr: sealed::Sealed {}

impl<T: ?Sized> sealed::Sealed for GpMutPtr<T> {}

impl<T: ?Sized> GpAnyMutPtr for GpMutPtr<T> {}

// === GpImmPtr === //

#[derive_where(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct GpImmPtr<T: ?Sized> {
    raw: GpMutPtr<T>,
}

impl<T: ?Sized> GpImmPtr<T> {
    pub fn new<'l>(value: T, arena: &GpArena<'l>) -> Self
    where
        T: Sized + 'l,
    {
        Self {
            raw: GpMutPtr::new(value, arena),
        }
    }

    pub unsafe fn new_unchecked(generation: GpGeneration, ptr: NonNull<T>) -> Self {
        unsafe {
            Self {
                raw: GpMutPtr::new_unchecked(generation, ptr),
            }
        }
    }
}

impl<T> GpImmPtr<[T]> {
    pub fn new_slice<'l>(value: &[T], arena: &GpArena<'l>) -> Self
    where
        T: Clone + 'l,
    {
        Self {
            raw: GpMutPtr::new_slice(value, arena),
        }
    }

    pub fn new_iter<'l>(
        value: impl IntoIterator<Item = T, IntoIter: ExactSizeIterator>,
        arena: &GpArena<'l>,
    ) -> Self
    where
        T: 'l,
    {
        Self {
            raw: GpMutPtr::new_iter(value, arena),
        }
    }
}

impl<T: ?Sized> GpImmPtr<T> {
    pub fn generation(self) -> GpGeneration {
        self.raw.generation()
    }

    pub fn map<V: ?Sized>(
        self,
        f: impl for<'a> FnOnce(&'a T) -> &'a V,
        arena: &GpArena<'_>,
    ) -> GpImmPtr<V> {
        let ptr = NonNull::from(f(self.r(arena)));

        GpImmPtr {
            raw: unsafe { GpMutPtr::new_unchecked(self.generation(), ptr) },
        }
    }

    pub fn ptr(self) -> NonNull<T> {
        self.raw.ptr()
    }

    pub fn r<'a>(self, arena: &'a GpArena<'_>) -> &'a T {
        self.raw.r(arena)
    }
}
