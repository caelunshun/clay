use crate::base::{Session, arena::Obj};

// === Type === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct Ty {
    inner: Obj<TyKind>,
}

impl Ty {
    pub fn new_unchecked(inner: Obj<TyKind>) -> Self {
        Self { inner }
    }

    pub fn kind(self, s: &Session) -> &TyKind {
        self.inner.r(s)
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct TyList {
    inner: Obj<[Ty]>,
}

impl TyList {
    pub fn new_unchecked(inner: Obj<[Ty]>) -> Self {
        Self { inner }
    }

    pub fn list(self, s: &Session) -> &[Ty] {
        self.inner.r(s)
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum TyKind {
    Never,
    Scalar,
    Struct,
    Pointer(Ty),
    Trait,
}
