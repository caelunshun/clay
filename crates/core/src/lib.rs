pub mod brick;
pub mod constants;
pub mod ghost_arena;
pub mod sexpr;

pub type FastHashMap<K, V> = hashbrown::HashMap<K, V, foldhash::fast::RandomState>;
pub type FastHashSet<T> = hashbrown::HashSet<T, foldhash::fast::RandomState>;

pub type FastIndexMap<K, V> = indexmap::IndexMap<K, V, foldhash::fast::RandomState>;
pub type FastIndexSet<T> = indexmap::IndexSet<T, foldhash::fast::RandomState>;
