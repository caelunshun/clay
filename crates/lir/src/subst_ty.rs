use crate::{
    arena::Ptr,
    ty_family::{TyFamily, TyParam},
};

/// Combination of an AbstractTy and a list of type arguments
/// with which to instantiate it, forming a concrete type after
/// substitution.
#[derive(Debug, Clone)]
pub enum SubstTy {
    TyParam(Ptr<TyParam>),
    Instantiation(InstantiationTy),
}

#[derive(Debug, Clone)]
pub struct InstantiationTy {
    pub ty_family: Ptr<TyFamily>,
    pub ty_args: Vec<Ptr<SubstTy>>,
}
