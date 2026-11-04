use crate::{
    base::{DiagCtxt, SessionInterners, SourceMap, SymbolInterner},
    utils::bump::{DropBump, ScratchBump},
};
use std::{cell::RefCell, fmt, ops::Deref, rc::Rc};

thread_local! {
    static SESSION_TLS: RefCell<Option<Session>> = const { RefCell::new(None) };
}

pub trait HasSession {
    fn session(&self) -> &Session;
}

#[derive(Clone)]
pub struct Session(Rc<SessionInner>);

pub struct SessionInner {
    pub symbols: SymbolInterner,
    pub diag: DiagCtxt,
    pub source_map: SourceMap,
    pub drop_bump: DropBump<'static>,
    pub scratch_bump: ScratchBump,
    pub interners: SessionInterners,
}

impl fmt::Debug for Session {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Session").finish_non_exhaustive()
    }
}

impl Session {
    #[expect(clippy::new_without_default)]
    pub fn new() -> Self {
        Self(Rc::new(SessionInner {
            symbols: SymbolInterner::default(),
            diag: DiagCtxt::default(),
            source_map: SourceMap::default(),
            drop_bump: DropBump::default(),
            scratch_bump: ScratchBump::default(),
            interners: SessionInterners::default(),
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
