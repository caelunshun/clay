use crate::{
    adt_family::{AdtTyFamily, TyParam},
    arena::Ptr,
    ty::prim::PrimTy,
};
use clay_core::FastIndexMap;

/// Allows forming a concrete type after substitution
/// of type parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubstTy {
    Self_,
    TyParam(Ptr<TyParam>),
    Prim(PrimTy),
    Slice(SliceSubstTy),
    Buffer(BufferSubstTy),
    Adt(AdtSubstTy),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdtSubstTy {
    pub adt_family: AdtTyFamily,
    pub ty_args: TyArgs,
}

pub type TyArgs = FastIndexMap<Ptr<TyParam>, SubstTy>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SliceSubstTy {
    pub element: Box<SubstTy>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BufferSubstTy {
    pub element: Box<SubstTy>,
}
