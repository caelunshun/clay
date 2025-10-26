pub mod db;
pub mod ident;
pub mod sexpr;

pub use db::Db;
use std::hash::BuildHasherDefault;

pub type HashMap<K, V> = std::collections::HashMap<K, V, BuildHasherDefault<rustc_hash::FxHasher>>;
pub type HashSet<T> = std::collections::HashSet<T, BuildHasherDefault<rustc_hash::FxHasher>>;

pub type IndexMap<K, V> = indexmap::IndexMap<K, V, BuildHasherDefault<rustc_hash::FxHasher>>;
pub type IndexSet<T> = indexmap::IndexSet<T, BuildHasherDefault<rustc_hash::FxHasher>>;
