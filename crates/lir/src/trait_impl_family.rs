use crate::{
    arena::Ptr,
    subst_func::SubstFunc,
    subst_trait::SubstTrait,
    subst_ty::SubstTy,
    trait_family::{AssocFuncFamily, AssocTyFamily},
    ty_param::TyParam,
};
use clay_core::FastIndexMap;

#[derive(Debug, Clone)]
pub struct TraitImplFamily {
    pub ty_params: Vec<Ptr<TyParam>>,
    pub trait_: SubstTrait,
    pub provided_tys: FastIndexMap<Ptr<AssocTyFamily>, SubstTy>,
    pub provided_funcs: FastIndexMap<Ptr<AssocFuncFamily>, SubstFunc>,
}
