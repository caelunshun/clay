use crate::{arena::Ptr, ty::prim::PrimTy};

pub mod prim;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    Prim(PrimTy),
    Slice(SliceTy),
    Buffer(BufferTy),
    Ref(RefTy),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SliceTy {
    pub element: Ptr<Ty>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BufferTy {
    pub element: Ptr<Ty>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct RefTy {
    pub pointee: Ptr<Ty>,
}
