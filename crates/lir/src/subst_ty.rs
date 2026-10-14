use crate::{adt_family::AdtTyFamily, arena::Ptr, ty::prim::PrimTy, ty_param::TyParam};
use clay_core::FastIndexMap;

/// Allows forming a concrete type after substitution
/// of type parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubstTy {
    Self_,
    TyParam(Ptr<TyParam>),
    Prim(PrimTy),
    Slice(SliceSubstTyRef),
    Buffer(BufferSubstTyRef),
    Adt(AdtSubstTyRef),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdtSubstTyRef {
    pub adt_family: AdtTyFamily,
    pub ty_args: SubstTyArgs,
}

pub type SubstTyArgs = FastIndexMap<Ptr<TyParam>, SubstTy>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SliceSubstTyRef {
    pub element: Box<SubstTy>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BufferSubstTyRef {
    pub element: Box<SubstTy>,
}
