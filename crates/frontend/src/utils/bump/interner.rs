use crate::utils::bump::{DropBump, DropBumpPtr, ScratchBump};
use bumpalo::collections::Vec as BumpVec;
use clay_core::FastHashMap;
use derive_where::derive_where;
use hashbrown::hash_map;
use std::{
    cell::RefCell,
    hash::{self, BuildHasher as _},
};

// === DropBumpValueInterner === //

#[derive_where(Default)]
pub struct DropBumpValueInterner<T> {
    interns: RefCell<FastHashMap<(DropBumpPtr<T>, u64), ()>>,
}

impl<T> DropBumpValueInterner<T>
where
    T: hash::Hash + Eq,
{
    pub fn intern<'l>(&self, value: T, drop_bump: &DropBump<'l>) -> DropBumpPtr<T>
    where
        T: 'l,
    {
        let mut interns = self.interns.borrow_mut();
        let hash = interns.hasher().hash_one(&value);

        match interns
            .raw_entry_mut()
            .from_hash(hash, |(other, other_hash)| {
                hash == *other_hash && &value == other.r(drop_bump)
            }) {
            hash_map::RawEntryMut::Occupied(entry) => entry.key().0,
            hash_map::RawEntryMut::Vacant(entry) => {
                let value = DropBumpPtr::new(value, drop_bump);
                entry.insert_with_hasher(hash, (value, hash), (), |(_, hash)| *hash);
                value
            }
        }
    }
}

// === DropBumpListInterner === //

#[derive_where(Default)]
pub struct DropBumpListInterner<T> {
    interns: RefCell<FastHashMap<(DropBumpPtr<[T]>, u64), ()>>,
}

impl<T> DropBumpListInterner<T>
where
    T: hash::Hash + Eq,
{
    pub fn intern<'l>(
        &self,
        values: impl IntoIterator<Item = T>,
        drop_bump: &DropBump<'l>,
        scratch_bump: &ScratchBump,
    ) -> DropBumpPtr<[T]>
    where
        T: 'l,
    {
        let scratch_bump = scratch_bump.acquire_guard();
        let values = BumpVec::from_iter_in(values, &scratch_bump);

        let mut interns = self.interns.borrow_mut();
        let hash = interns.hasher().hash_one(&values);

        match interns
            .raw_entry_mut()
            .from_hash(hash, |(other, other_hash)| {
                hash == *other_hash && values == other.r(drop_bump)
            }) {
            hash_map::RawEntryMut::Occupied(entry) => entry.key().0,
            hash_map::RawEntryMut::Vacant(entry) => {
                let values = DropBumpPtr::new_iter_exact(values, drop_bump);
                entry.insert_with_hasher(hash, (values, hash), (), |(_, hash)| *hash);
                values
            }
        }
    }
}
