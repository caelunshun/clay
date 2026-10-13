use arrayvec::ArrayVec;
use derive_where::derive_where;
use std::{
    array,
    cell::UnsafeCell,
    mem::{self, MaybeUninit, offset_of},
    ptr::NonNull,
    sync::{Mutex, atomic::AtomicU64},
};

pub struct Arena<T> {
    inner: Mutex<Inner<T>>,
    generation: u32,
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        static NEXT_GENERATION: AtomicU64 = AtomicU64::new(0);

        let generation = NEXT_GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let generation = u32::try_from(generation).expect("created more than 2^32 arenas");

        Self {
            inner: Mutex::new(Inner {
                blocks: Vec::new(),
                free_list: Vec::new(),
            }),
            generation,
        }
    }

    /// Inserts with exclusive access to the arena.
    #[inline]
    pub fn insert(&mut self, value: T) -> Ptr<T> {
        let inner = self.inner.get_mut().unwrap();
        let [index] = inner.alloc_indexes::<1>();
        unsafe {
            Self::insert_with_index_unchecked(value, index, |b| &*inner.blocks[b], self.generation)
        }
    }

    #[inline]
    unsafe fn insert_with_index_unchecked<'a>(
        value: T,
        index: usize,
        get_block: impl Fn(usize) -> &'a Block<T>,
        arena_generation: u32,
    ) -> Ptr<T>
    where
        T: 'a,
    {
        let (block_idx, slot_idx) = split_index(index);

        let slot = unsafe { &mut *get_block(block_idx).slots[slot_idx].get() };
        slot.value.write(value);
        Ptr {
            slot_generation: slot.generation,
            arena_generation,
            slot: NonNull::from(slot),
        }
    }

    /// Removes an entry from the arena, freeing its slot.
    #[inline]
    pub fn remove(&mut self, mut ptr: Ptr<T>) -> T {
        assert_eq!(ptr.arena_generation, self.generation);
        unsafe {
            let slot = ptr.slot.as_mut();
            assert_eq!(slot.generation, ptr.slot_generation);
            let global_index = slot.block_index() * BLOCK_SIZE + slot.idx_within_block as usize;
            slot.generation += 1;
            if slot.generation != u32::MAX {
                self.inner.get_mut().unwrap().free_list.push(global_index);
            }

            slot.value.assume_init_read()
        }
    }

    pub fn create_inserter<'a>(&'a self) -> ArenaInserter<'a, T> {
        ArenaInserter {
            arena: self,
            block_ptr_cache: Vec::new(),
            local_free_list: Box::new(ArrayVec::new()),
        }
    }
}

const LOCAL_FREE_LIST_CAPACITY: usize = 32;

/// Allows inserting values to an arena in concurrent threads.
pub struct ArenaInserter<'a, T> {
    arena: &'a Arena<T>,
    block_ptr_cache: Vec<&'a Block<T>>,
    local_free_list: Box<ArrayVec<usize, LOCAL_FREE_LIST_CAPACITY>>,
}

impl<'a, T> ArenaInserter<'a, T> {
    #[inline]
    pub fn insert(&mut self, value: T) -> Ptr<T> {
        let index = match self.local_free_list.pop() {
            Some(index) => index,
            None => {
                let mut inner = self.arena.inner.lock().unwrap();
                let free = inner.alloc_indexes::<{ LOCAL_FREE_LIST_CAPACITY + 1 }>();

                self.block_ptr_cache = inner
                    .blocks
                    .iter()
                    .map(|block_box| unsafe {
                        mem::transmute::<&'_ Block<T>, &'a Block<T>>(block_box)
                    })
                    .collect();

                self.local_free_list.extend(free[1..].iter().copied());
                free[0]
            }
        };

        unsafe {
            Arena::<T>::insert_with_index_unchecked(
                value,
                index,
                |b| self.block_ptr_cache[b],
                self.arena.generation,
            )
        }
    }
}

impl<'a, T> Drop for ArenaInserter<'a, T> {
    fn drop(&mut self) {
        if !self.local_free_list.is_empty() {
            // Return leftover free list entries
            self.arena
                .inner
                .lock()
                .unwrap()
                .free_list
                .extend_from_slice(&self.local_free_list);
        }
    }
}

fn split_index(index: usize) -> (usize, usize) {
    (index / BLOCK_SIZE, index % BLOCK_SIZE)
}

struct Inner<T> {
    blocks: Vec<Box<Block<T>>>,
    free_list: Vec<usize>,
}

impl<T> Inner<T> {
    pub fn alloc_indexes<const N: usize>(&mut self) -> [usize; N] {
        let mut indexes: ArrayVec<usize, N> = (0..self.free_list.len().min(N))
            .map(|_| self.free_list.pop().unwrap())
            .collect();

        while indexes.len() < N {
            let first = self.allocate_new_block();
            let needed = N - indexes.len();
            indexes.extend((first..first + BLOCK_SIZE).take(needed));
            if needed < BLOCK_SIZE {
                self.free_list
                    .extend((first + needed)..(first + BLOCK_SIZE));
            }
        }

        indexes.as_slice().try_into().unwrap()
    }

    // Returns index of the first slot in the block.
    fn allocate_new_block(&mut self) -> usize {
        let index = self.blocks.len();
        self.blocks.push(Box::new(Block {
            index,
            slots: array::from_fn(|i| {
                UnsafeCell::new(Slot {
                    value: MaybeUninit::uninit(),
                    generation: 0,
                    idx_within_block: i.try_into().unwrap(),
                })
            }),
        }));
        index * BLOCK_SIZE
    }
}

const BLOCK_SIZE: usize = 1024;

#[repr(C)]
struct Block<T> {
    slots: [UnsafeCell<Slot<T>>; BLOCK_SIZE],
    index: usize,
}

unsafe impl<T> Send for Block<T> where T: Send {}
unsafe impl<T> Sync for Block<T> where T: Send + Sync {}

struct Slot<T> {
    value: MaybeUninit<T>,
    idx_within_block: u32,
    generation: u32,
}

impl<T> Slot<T> {
    pub unsafe fn block_index(&self) -> usize {
        unsafe {
            let this = self as *const Self;
            let base = this
                .cast::<u8>()
                .offset(-(size_of::<Self>() as isize * self.idx_within_block as isize));
            base.add(offset_of!(Block<T>, index)).cast::<usize>().read()
        }
    }
}

#[derive_where(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Ptr<T> {
    slot: NonNull<Slot<T>>,
    slot_generation: u32,
    arena_generation: u32,
}

unsafe impl<T> Send for Ptr<T> {}
unsafe impl<T> Sync for Ptr<T> {}

impl<T> Ptr<T> {
    #[inline]
    pub fn is_alive(&self, ar: &Arena<T>) -> bool {
        assert_eq!(self.arena_generation, ar.generation);
        unsafe { self.slot.as_ref().generation == self.slot_generation }
    }

    #[inline]
    pub fn r(self, ar: &Arena<T>) -> &T {
        assert_eq!(self.arena_generation, ar.generation);
        unsafe {
            let slot = self.slot.as_ref();
            assert_eq!(slot.generation, self.slot_generation);
            slot.value.assume_init_ref()
        }
    }

    #[inline]
    pub fn m(self, ar: &mut Arena<T>) -> &mut T {
        assert_eq!(self.arena_generation, ar.generation);
        unsafe {
            let slot = &mut *self.slot.as_ptr();
            assert_eq!(slot.generation, self.slot_generation);
            slot.value.assume_init_mut()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let mut ar = Arena::<u32>::new();

        let v0 = ar.insert(0);
        let v1 = ar.insert(1);

        assert_eq!(v0.r(&ar), &0);
        assert_eq!(v1.r(&ar), &1);

        *v1.m(&mut ar) = 2;

        assert_eq!(v0.r(&ar), &0);
        assert_eq!(v1.r(&ar), &2);

        ar.remove(v1);
        assert!(!v1.is_alive(&ar));
        assert!(v0.is_alive(&ar));

        let v2 = ar.insert(3);
        assert_eq!(v2.r(&ar), &3);
        assert!(!v1.is_alive(&ar));
    }

    #[test]
    fn inserter() {
        let ar = Arena::<u32>::new();

        let mut ptrs = Vec::new();

        for i in 0..10 {
            let mut inserter = ar.create_inserter();
            for j in 0..100 {
                ptrs.push(inserter.insert(j + i * 100));
            }
        }

        for (i, ptr) in ptrs.into_iter().enumerate() {
            assert_eq!(ptr.r(&ar), &(i as u32));
        }
    }
}
