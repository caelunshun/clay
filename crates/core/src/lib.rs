pub mod constants;
pub mod db;
pub mod ident;
pub mod sexpr;

use allocator_api2::alloc::Global;
pub use db::Db;

pub type HashMap<K, V, A = Global> = hashbrown::HashMap<K, V, hashbrown::DefaultHashBuilder, A>;
pub type HashSet<T, A = Global> = hashbrown::HashSet<T, hashbrown::DefaultHashBuilder, A>;

pub type IndexMap<K, V> = indexmap::IndexMap<K, V, hashbrown::DefaultHashBuilder>;
pub type IndexSet<T> = indexmap::IndexSet<T, hashbrown::DefaultHashBuilder>;
