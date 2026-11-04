use crate::utils::bump::ScratchBump;
use bumpalo::{Bump, collections::Vec as BumpVec};
use derive_where::derive_where;
use std::{
    cell::RefCell,
    fmt,
    num::NonZeroU64,
    ptr::NonNull,
    sync::atomic::{AtomicU64, Ordering::Relaxed},
};

// === DropBump === //

trait Anything {}

impl<T: ?Sized> Anything for T {}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct DropGeneration(NonZeroU64);

pub struct DropBump<'a> {
    generation: DropGeneration,
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

impl fmt::Debug for DropBump<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DropBump").finish_non_exhaustive()
    }
}

impl Default for DropBump<'_> {
    fn default() -> Self {
        static ID_GEN: AtomicU64 = AtomicU64::new(1);

        let generation = DropGeneration(NonZeroU64::new(ID_GEN.fetch_add(1, Relaxed)).unwrap());

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

impl<'l> DropBump<'l> {
    pub fn generation(&self) -> DropGeneration {
        self.generation
    }
}

impl Drop for DropBump<'_> {
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

// === DropBumpPtr === //

#[derive_where(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[repr(C)]
pub struct DropBumpPtr<T: ?Sized> {
    generation: DropGeneration,
    ptr: NonNull<T>,
}

impl<T: ?Sized> DropBumpPtr<T> {
    pub unsafe fn new_unchecked(generation: DropGeneration, ptr: NonNull<T>) -> Self {
        Self { generation, ptr }
    }

    pub fn new<'l>(value: T, drop_bump: &DropBump<'l>) -> Self
    where
        T: Sized + 'l,
    {
        let ptr = NonNull::from(drop_bump.bump.alloc(value));

        drop_bump.drop_queue.borrow_mut().singles.push(ptr);

        Self {
            generation: drop_bump.generation,
            ptr,
        }
    }
}

impl<T> DropBumpPtr<[T]> {
    pub fn new_list_empty(drop_bump: &DropBump<'_>) -> Self {
        Self {
            generation: drop_bump.generation,
            ptr: NonNull::slice_from_raw_parts(NonNull::dangling(), 0),
        }
    }

    pub unsafe fn new_list_raw<'l>(
        f: impl FnOnce(&Bump) -> &mut [T],
        drop_bump: &DropBump<'_>,
    ) -> Self
    where
        T: 'l,
    {
        let ptr = NonNull::from(f(&drop_bump.bump));

        if ptr.is_empty() {
            return Self::new_list_empty(drop_bump);
        }

        drop_bump.drop_queue.borrow_mut().lists.push(DropQueueList {
            base: ptr.cast(),
            len: ptr.len(),
            drop: |ptr, len| unsafe {
                NonNull::slice_from_raw_parts(ptr.cast::<T>(), len).drop_in_place();
            },
        });

        Self {
            generation: drop_bump.generation,
            ptr,
        }
    }

    pub fn new_slice_clone<'l>(values: &[T], drop_bump: &DropBump<'l>) -> Self
    where
        T: 'l + Clone,
    {
        if values.is_empty() {
            return Self::new_list_empty(drop_bump);
        }

        unsafe { Self::new_list_raw(|bump| bump.alloc_slice_clone(values), drop_bump) }
    }

    pub fn new_slice_copy<'l>(values: &[T], drop_bump: &DropBump<'l>) -> Self
    where
        T: 'l + Copy,
    {
        if values.is_empty() {
            return Self::new_list_empty(drop_bump);
        }

        unsafe { Self::new_list_raw(|bump| bump.alloc_slice_copy(values), drop_bump) }
    }

    pub fn new_iter<'l>(
        values: impl IntoIterator<Item = T>,
        drop_bump: &DropBump<'l>,
        scratch_bump: &ScratchBump,
    ) -> Self
    where
        T: 'l,
    {
        let values = values.into_iter();
        let size_hint = values.size_hint();

        if let (low, Some(high)) = size_hint
            && low == high
        {
            return Self::new_iter_assume_exact(low, values, drop_bump);
        }

        scratch_bump.acquire(|scratch_bump| {
            let values = BumpVec::from_iter_in(values, scratch_bump);
            Self::new_iter_exact(values, drop_bump)
        })
    }

    pub fn new_iter_exact<'l>(
        values: impl IntoIterator<Item = T, IntoIter: ExactSizeIterator>,
        drop_bump: &DropBump<'l>,
    ) -> Self
    where
        T: 'l,
    {
        let values = values.into_iter();
        Self::new_iter_assume_exact(values.len(), values, drop_bump)
    }

    fn new_iter_assume_exact<'l>(
        values_len: usize,
        values: impl IntoIterator<Item = T>,
        drop_bump: &DropBump<'l>,
    ) -> Self
    where
        T: 'l,
    {
        let mut values = values.into_iter();

        Self::new_iter_with(
            values_len,
            |_| values.next().expect("Iterator supplied too few elements"),
            drop_bump,
        )
    }

    pub fn new_iter_with<'l>(
        len: usize,
        f: impl FnMut(usize) -> T,
        drop_bump: &DropBump<'l>,
    ) -> Self
    where
        T: 'l,
    {
        if len == 0 {
            return Self::new_list_empty(drop_bump);
        }

        unsafe { Self::new_list_raw(|bump| bump.alloc_slice_fill_with(len, f), drop_bump) }
    }
}

impl<T: ?Sized> DropBumpPtr<T> {
    pub fn generation(self) -> DropGeneration {
        self.generation
    }

    pub fn ptr(self) -> NonNull<T> {
        self.ptr
    }

    pub fn r<'a>(self, drop_bump: &'a DropBump<'_>) -> &'a T {
        assert_eq!(drop_bump.generation, self.generation);

        unsafe { self.ptr.as_ref() }
    }

    pub fn map<V: ?Sized>(
        self,
        f: impl for<'a> FnOnce(&'a T) -> &'a V,
        drop_bump: &DropBump<'_>,
    ) -> DropBumpPtr<V> {
        let ptr = NonNull::from(f(self.r(drop_bump)));

        unsafe { DropBumpPtr::new_unchecked(self.generation(), ptr) }
    }
}
