use crate::{
    base::Session,
    utils::hash::{FxHashMap, fx_hash_one, hash_map},
};
use bumpalo::Bump;
use std::{cell::RefCell, fmt, num::NonZeroU32};

// === Symbol === //

#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Symbol(NonZeroU32);

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}#{}", self.as_str(&Session::fetch()), self.0)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str(&Session::fetch()))
    }
}

impl Symbol {
    pub fn new(value: &str) -> Self {
        Session::fetch().symbols.intern(value)
    }

    pub fn as_str(self, s: &Session) -> &str {
        s.symbols.lookup(self)
    }
}

// === SymbolInterner === //

#[derive(Default)]
pub struct SymbolInterner(RefCell<SymbolInternInner>);

#[derive(Default)]
struct SymbolInternInner {
    arena: Bump,
    symbols: Vec<*const str>,
    symbol_map: FxHashMap<(u64, *const str), Symbol>,
}

impl fmt::Debug for SymbolInterner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SymbolInterner").finish_non_exhaustive()
    }
}

impl SymbolInterner {
    pub fn intern(&self, value: &str) -> Symbol {
        let hash = fx_hash_one(value);

        let mut inner = self.0.borrow_mut();
        let inner = &mut *inner;

        let entry =
            inner
                .symbol_map
                .raw_entry_mut()
                .from_hash(hash, |&(candidate_hash, candidate)| {
                    candidate_hash == hash && unsafe { *candidate == *value }
                });

        match entry {
            hash_map::RawEntryMut::Occupied(entry) => *entry.get(),
            hash_map::RawEntryMut::Vacant(entry) => {
                let str = inner.arena.alloc_str(value);
                let sym = Symbol(
                    u32::try_from(inner.symbols.len() + 1)
                        .ok()
                        .and_then(NonZeroU32::new)
                        .expect("too many symbols"),
                );
                inner.symbols.push(str);
                entry.insert_with_hasher(hash, (hash, str), sym, |&(hash, _)| hash);
                sym
            }
        }
    }

    pub fn lookup(&self, sym: Symbol) -> &str {
        let inner = self.0.borrow();

        unsafe { &*inner.symbols[(sym.0.get() - 1) as usize] }
    }
}

// === `symbol` macro === //

// FIXME: This is incorrect for multi-session.
#[doc(hidden)]
pub mod symbol_internals {
    pub use super::{Symbol, symbol};
    pub use std::primitive::str;
    use std::{
        num::NonZeroU32,
        sync::atomic::{AtomicU32, Ordering::*},
    };

    pub struct LateSymbol {
        id: AtomicU32,
    }

    impl LateSymbol {
        #[allow(clippy::new_without_default)] // (macro internal)
        pub const fn new() -> Self {
            Self {
                id: AtomicU32::new(0),
            }
        }

        pub fn get(&self, init: &str) -> Symbol {
            if let Some(sym) = NonZeroU32::new(self.id.load(Relaxed)) {
                return Symbol(sym);
            }

            let sym = Symbol::new(init);
            self.id.store(sym.0.get(), Relaxed);
            sym
        }
    }
}

#[macro_export]
macro_rules! symbol {
    (fn $text:expr) => {{
        fn _symbol_getter() -> $crate::base::syntax::symbol_internals::Symbol {
            static LATE: $crate::base::syntax::symbol_internals::LateSymbol =
                $crate::base::syntax::symbol_internals::LateSymbol::new();

            const INIT: &'static $crate::base::syntax::symbol_internals::str = $text;

            LATE.get(INIT)
        }

        _symbol_getter
    }};
    ($text:expr) => {{
        $crate::base::syntax::symbol_internals::symbol!(fn $text)()
    }};
}

pub use symbol;
