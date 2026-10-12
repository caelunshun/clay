use crate::utils::hash::FxHashMap;
use derive_where::derive_where;
use std::hash;

#[derive(Debug, Clone)]
#[derive_where(Default)]
pub struct NameResolver<K, T> {
    depth: u32,
    map: FxHashMap<K, DefinedName<T>>,
    stack: Vec<Op<K, T>>,
}

#[derive(Debug, Copy, Clone)]
pub struct DefinedName<T> {
    pub depth: u32,
    pub value: T,
}

#[derive(Debug, Clone)]
enum Op<K, T> {
    Set(K, Option<DefinedName<T>>),
    Rib,
}

impl<K, T> NameResolver<K, T>
where
    K: Copy + hash::Hash + Eq,
    T: Copy,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, sym: K, value: T) -> Option<DefinedName<T>> {
        let replaced = self.map.insert(
            sym,
            DefinedName {
                depth: self.depth,
                value,
            },
        );

        self.stack.push(Op::Set(sym, replaced));

        replaced
    }

    pub fn lookup(&self, sym: K) -> Option<&T> {
        self.map.get(&sym).map(|v| &v.value)
    }

    pub fn push_rib(&mut self) {
        self.depth += 1;
        self.stack.push(Op::Rib);
    }

    pub fn pop_rib(&mut self) {
        self.depth -= 1;

        while let Some(op) = self.stack.pop() {
            let Op::Set(sym, prev) = op else {
                // Hit the previous `push`.
                break;
            };

            if let Some(prev) = prev {
                self.map.insert(sym, prev);
            } else {
                self.map.remove(&sym);
            }
        }
    }
}
