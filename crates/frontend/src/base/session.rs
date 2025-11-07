use crate::base::{
    DiagCtxt,
    arena::GpArena,
    syntax::{SourceMap, SymbolInterner},
};
use std::{cell::RefCell, ops::Deref, rc::Rc};

thread_local! {
    static SESSION_TLS: RefCell<Option<Session>> = const { RefCell::new(None) };
}

pub trait HasSession {
    fn session(&self) -> &Session;
}

#[derive(Debug, Clone)]
pub struct Session(Rc<SessionInner>);

#[derive(Debug)]
pub struct SessionInner {
    pub symbols: SymbolInterner,
    pub diag: DiagCtxt,
    pub source_map: SourceMap,
    pub gp_arena: GpArena,
}

impl Session {
    #[expect(clippy::new_without_default)]
    pub fn new() -> Self {
        Self(Rc::new(SessionInner {
            symbols: SymbolInterner::default(),
            diag: DiagCtxt::default(),
            source_map: SourceMap::default(),
            gp_arena: GpArena::default(),
        }))
    }

    #[must_use]
    pub fn bind(self) -> impl Sized {
        let old = SESSION_TLS.replace(Some(self));

        scopeguard::guard(old, move |old| {
            SESSION_TLS.set(old);
        })
    }

    pub fn fetch() -> Session {
        SESSION_TLS
            .with_borrow(|v| v.clone())
            .expect("no session was ever bound")
    }
}

impl Deref for Session {
    type Target = SessionInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl HasSession for Session {
    fn session(&self) -> &Session {
        self
    }
}
