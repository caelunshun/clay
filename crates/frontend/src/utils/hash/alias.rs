use hashbrown::{HashMap, HashSet};
pub use rustc_hash::FxHasher;
use std::hash::{self, BuildHasher, BuildHasherDefault, Hash, Hasher};

pub type FxBuildHasher = BuildHasherDefault<FxHasher>;
pub type FxHashMap<K, V> = HashMap<K, V, FxBuildHasher>;
pub type FxHashSet<T> = HashSet<T, FxBuildHasher>;

pub fn fx_hash_one(v: impl hash::Hash) -> u64 {
    let mut hasher = FxHasher::default();
    v.hash(&mut hasher);
    hasher.finish()
}

pub trait IterHashExt: BuildHasher {
    fn hash_one_iter(&self, iter: impl IntoIterator<Item: Hash>) -> u64 {
        let mut hasher = self.build_hasher();
        let mut len = 0;

        for item in iter {
            item.hash(&mut hasher);
            len += 1;
        }

        hasher.write_usize(len);
        hasher.finish()
    }
}

impl<B: ?Sized + BuildHasher> IterHashExt for B {}
