use crate::{adt_family::TyParam, arena::Ptr, subst_ty::SubstTy};

#[derive(Debug, Clone)]
pub struct SigFamily {
    pub ty_params: Vec<Ptr<TyParam>>,
    pub param_tys: Vec<SubstTy>,
    pub ret_ty: SubstTy,
}
