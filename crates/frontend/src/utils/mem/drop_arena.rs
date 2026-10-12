use bumpalo::Bump;
use derive_where::derive_where;
use std::{
    cell::RefCell,
    fmt,
    num::NonZeroU64,
    ptr::NonNull,
    sync::atomic::{AtomicU64, Ordering::Relaxed},
};

// === DropArena === //

trait Anything {}

impl<T: ?Sized> Anything for T {}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct GpGeneration(NonZeroU64);

pub struct DropArena<'a> {
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

impl fmt::Debug for DropArena<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GpArena").finish_non_exhaustive()
    }
}

impl Default for DropArena<'_> {
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

impl<'l> DropArena<'l> {
    pub fn generation(&self) -> GpGeneration {
        self.generation
    }
}

impl Drop for DropArena<'_> {
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

// === DropArenaPtr === //

#[derive_where(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[repr(C)]
pub struct DropArenaPtr<T: ?Sized> {
    generation: GpGeneration,
    ptr: NonNull<T>,
}

impl<T: ?Sized> DropArenaPtr<T> {
    pub fn new<'l>(value: T, arena: &DropArena<'l>) -> Self
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
}

impl<T> DropArenaPtr<[T]> {
    pub fn new_slice<'l>(value: &[T], arena: &DropArena<'l>) -> Self
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
        arena: &DropArena<'l>,
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

impl<T: ?Sized> DropArenaPtr<T> {
    pub fn generation(self) -> GpGeneration {
        self.generation
    }

    pub fn ptr(self) -> NonNull<T> {
        self.ptr
    }

    pub fn r<'a>(self, arena: &'a DropArena<'_>) -> &'a T {
        assert_eq!(arena.generation, self.generation);

        unsafe { self.ptr.as_ref() }
    }

    pub fn map<V: ?Sized>(
        self,
        f: impl for<'a> FnOnce(&'a T) -> &'a V,
        arena: &DropArena<'_>,
    ) -> DropArenaPtr<V> {
        let ptr = NonNull::from(f(self.r(arena)));

        unsafe { DropArenaPtr::new_unchecked(self.generation(), ptr) }
    }
}
