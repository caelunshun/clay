use crate::{arena::Ptr, subst_ty::SubstTyArgs, trait_family::TraitFamily};

/// A concrete trait instance.
///
/// Note that types are still `SubstTy` because they may refer
/// to `Self` and have type parameters themselves.
#[derive(Debug, Clone)]
pub struct SubstTrait {
    pub ty_args: SubstTyArgs,
    pub family: Ptr<TraitFamily>,
}
