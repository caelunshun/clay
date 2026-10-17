use crate::{adt_family::AdtTyFamily, arena::Ptr, ty::prim::PrimTy, ty_param::TyParam};
use clay_core::FastIndexMap;

/// Allows forming a concrete type after substitution
/// of type parameters.
#[derive(Debug, Clone)]
pub enum SubstTy {
    Self_,
    TyParam(Ptr<TyParam>),
    Prim(PrimTy),
    Slice(SliceSubstTyRef),
    Buffer(BufferSubstTyRef),
    Adt(AdtSubstTyRef),
}

#[derive(Debug, Clone)]
pub struct AdtSubstTyRef {
    pub adt_family: Ptr<AdtTyFamily>,
    pub ty_args: SubstTyArgs,
}

pub type SubstTyArgs = Box<FastIndexMap<Ptr<TyParam>, SubstTy>>;

#[derive(Debug, Clone)]
pub struct SliceSubstTyRef {
    pub element: Box<SubstTy>,
}

#[derive(Debug, Clone)]
pub struct BufferSubstTyRef {
    pub element: Box<SubstTy>,
}
