use crate::{
    base::{Diag, ErrorGuaranteed},
    utils::hash::{FxHashMap, hash_map},
};
use derive_where::derive_where;
use std::{cell::RefCell, hash, rc::Rc};

#[derive_where(Debug, Clone, Default)]
pub struct Memo<K, V> {
    #[expect(clippy::type_complexity)]
    #[derive_where(skip)]
    entries: Rc<RefCell<FxHashMap<K, Option<Result<V, ErrorGuaranteed>>>>>,
}

impl<K, V> Memo<K, V>
where
    K: Clone + hash::Hash + Eq,
    V: Clone,
{
    pub fn compute_infallible(&self, key: K, f: impl FnOnce(&K) -> V) -> V {
        self.compute(key, |i| Ok(f(i))).unwrap()
    }

    pub fn compute(
        &self,
        key: K,
        f: impl FnOnce(&K) -> Result<V, ErrorGuaranteed>,
    ) -> Result<V, ErrorGuaranteed> {
        match self.entries.borrow_mut().entry(key.clone()) {
            hash_map::Entry::Occupied(entry) => {
                return match entry.get() {
                    Some(v) => v.clone(),
                    None => Err(Diag::anon_err("cycle detected :(").emit()),
                };
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(None);
            }
        }

        let value = f(&key);
        self.entries.borrow_mut().insert(key, Some(value.clone()));
        value
    }
}
