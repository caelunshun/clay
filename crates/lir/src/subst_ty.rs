use crate::{
    adt_family::{AdtTyFamily, TyParam},
    arena::Ptr,
    ty::prim::PrimTy,
};

/// Allows forming a concrete type after substitution
/// of type parameters.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SubstTy {
    TyParam(Ptr<TyParam>),
    Prim(PrimTy),
    Slice(SliceSubstTy),
    Buffer(BufferSubstTy),
    Adt(AdtSubstTy),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AdtSubstTy {
    pub adt_family: AdtTyFamily,
    pub ty_args: Vec<SubstTy>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SliceSubstTy {
    pub element: Box<SubstTy>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BufferSubstTy {
    pub element: Box<SubstTy>,
}
