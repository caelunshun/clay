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
    pub fn intern_iter<'l>(
        &self,
        values: impl IntoIterator<Item = T>,
        drop_bump: &DropBump<'l>,
        scratch_bump: &ScratchBump,
    ) -> DropBumpPtr<[T]>
    where
        T: 'l,
    {
        let scratch = scratch_bump.acquire_guard();
        let values = BumpVec::from_iter_in(values, &scratch);

        self.intern_raw(
            values,
            |v| v.as_slice(),
            DropBumpPtr::new_iter_exact,
            drop_bump,
        )
    }

    pub fn intern_slice_clone<'l>(&self, values: &[T], drop_bump: &DropBump<'l>) -> DropBumpPtr<[T]>
    where
        T: 'l + Clone,
    {
        self.intern_raw(values, |v| *v, DropBumpPtr::new_slice_clone, drop_bump)
    }

    pub fn intern_slice_copy<'l>(&self, values: &[T], drop_bump: &DropBump<'l>) -> DropBumpPtr<[T]>
    where
        T: 'l + Copy,
    {
        self.intern_raw(values, |v| *v, DropBumpPtr::new_slice_copy, drop_bump)
    }

    pub fn intern_raw<'l, V>(
        &self,
        values: V,
        borrow: impl FnOnce(&V) -> &[T],
        alloc: impl FnOnce(V, &DropBump<'l>) -> DropBumpPtr<[T]>,
        drop_bump: &DropBump<'l>,
    ) -> DropBumpPtr<[T]>
    where
        T: 'l,
    {
        let values_slice = borrow(&values);

        if values_slice.is_empty() {
            return DropBumpPtr::new_list_empty(drop_bump);
        }

        let mut interns = self.interns.borrow_mut();
        let hash = interns.hasher().hash_one(&values_slice);

        match interns
            .raw_entry_mut()
            .from_hash(hash, |(other, other_hash)| {
                hash == *other_hash && values_slice == other.r(drop_bump)
            }) {
            hash_map::RawEntryMut::Occupied(entry) => entry.key().0,
            hash_map::RawEntryMut::Vacant(entry) => {
                let values = alloc(values, drop_bump);
                entry.insert_with_hasher(hash, (values, hash), (), |(_, hash)| *hash);
                values
            }
        }
    }
}
