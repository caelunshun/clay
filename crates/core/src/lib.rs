pub mod constants;
pub mod sexpr;

pub type FastHashMap<K, V> = hashbrown::HashMap<K, V, hashbrown::DefaultHashBuilder>;
pub type FastHashSet<T> = hashbrown::HashSet<T, hashbrown::DefaultHashBuilder>;

pub type FastIndexMap<K, V> = indexmap::IndexMap<K, V, hashbrown::DefaultHashBuilder>;
pub type FastIndexSet<T> = indexmap::IndexSet<T, hashbrown::DefaultHashBuilder>;
