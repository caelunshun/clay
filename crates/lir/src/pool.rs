use crate::error::Error;
use derive_where::derive_where;
use std::marker::PhantomData;

/// Pool of values of type `T` indexed by 32-bit indexes (`Pooled<T>`) without generations.
///
/// Downsides:
/// - Does not use generations in release mode. Use-after-free is a logic error.
/// - Supports at most 2^32 entries.
#[derive(Debug, Clone)]
#[derive_where(Default)]
pub struct LocalPool<T> {
    entries: Vec<Slot<T>>,
    free_indexes: Vec<u32>,
}

#[derive(Debug, Clone)]
struct Slot<T> {
    val: T,
    #[cfg(debug_assertions)]
    generation: u64,
}

#[derive_where(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Pooled<T> {
    index: u32,
    #[cfg(debug_assertions)]
    generation: u64,
    _marker: PhantomData<T>,
}

impl<T> LocalPool<T> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc(&mut self, value: T) -> Result<Pooled<T>, Error> {
        match self.free_indexes.pop() {
            Some(index) => {
                self.entries[index as usize].val = value;
                Ok(Pooled {
                    index,
                    #[cfg(debug_assertions)]
                    generation: self.entries[index as usize].generation,
                    _marker: PhantomData,
                })
            }
            None => {
                let index: u32 = self
                    .entries
                    .len()
                    .try_into()
                    .map_err(|_| Error::ArenaIndexOverflow)?;
                self.entries.push(Slot {
                    val: value,
                    #[cfg(debug_assertions)]
                    generation: 0,
                });
                Ok(Pooled {
                    index,
                    #[cfg(debug_assertions)]
                    generation: 0,
                    _marker: PhantomData,
                })
            }
        }
    }

    pub fn free(&mut self, slot: Pooled<T>) {
        #[cfg(debug_assertions)]
        {
            self.entries[slot.index as usize].generation += 1;
        }
        self.free_indexes.push(slot.index);
    }
}

impl<T> Pooled<T> {
    pub fn r(self, pool: &LocalPool<T>) -> &T {
        #[cfg(debug_assertions)]
        {
            assert_eq!(
                self.generation,
                pool.entries[self.index as usize].generation
            );
        }
        &pool.entries[self.index as usize].val
    }

    pub fn m(self, pool: &mut LocalPool<T>) -> &mut T {
        #[cfg(debug_assertions)]
        {
            assert_eq!(
                self.generation,
                pool.entries[self.index as usize].generation
            );
        }
        &mut pool.entries[self.index as usize].val
    }
}
