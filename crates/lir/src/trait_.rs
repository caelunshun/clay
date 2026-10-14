use crate::{
    arena::Ptr,
    trait_family::{AssocFuncFamily, AssocTyFamily},
};

/// A concrete trait instance, having no type parameters.
///
/// Note that types are still `SubstTy` because they may refer
/// to `Self` and have type parameters themselves.
#[derive(Debug, Clone)]
pub struct Trait {
    pub assoc_tys: Vec<Ptr<AssocTyFamily>>,
    pub assoc_funcs: Vec<Ptr<AssocFuncFamily>>,
}
