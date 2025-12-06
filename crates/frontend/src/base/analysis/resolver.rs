use crate::{
    base::{ErrorGuaranteed, syntax::Symbol},
    utils::hash::FxHashMap,
};
use derive_where::derive_where;

#[derive(Debug, Clone)]
#[derive_where(Default)]
pub struct NameResolver<T> {
    depth: u32,
    map: FxHashMap<Symbol, DefinedName<T>>,
    stack: Vec<Op<T>>,
}

#[derive(Debug, Copy, Clone)]
struct DefinedName<T> {
    depth: u32,
    value: T,
}

#[derive(Debug, Clone)]
enum Op<T> {
    Set(Symbol, Option<DefinedName<T>>),
    Rib,
}

impl<T: Copy> NameResolver<T> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(
        &mut self,
        sym: Symbol,
        value: T,
        on_shadow: impl FnOnce(T) -> ErrorGuaranteed,
    ) -> Option<ErrorGuaranteed> {
        if let Some(replaced) = self.define_inner(sym, value)
            && replaced.depth == self.depth
        {
            return Some(on_shadow(replaced.value));
        }

        None
    }

    pub fn define_force_shadow(&mut self, sym: Symbol, value: T) {
        self.define_inner(sym, value);
    }

    fn define_inner(&mut self, sym: Symbol, value: T) -> Option<DefinedName<T>> {
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

    pub fn lookup(&self, sym: Symbol) -> Option<&T> {
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
