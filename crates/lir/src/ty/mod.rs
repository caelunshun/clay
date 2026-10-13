use crate::{arena::Ptr, ty_family::TyFamily};

pub mod prim;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SliceTy {
    pub element: Ptr<TyFamily>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BufferTy {
    pub element: Ptr<TyFamily>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct RefTy {
    pub pointee: Ptr<TyFamily>,
}
