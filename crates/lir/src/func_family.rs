use crate::{arena::Ptr, subst_ty::SubstTy, ty_param::TyParam};

#[derive(Debug, Clone)]
pub struct FuncFamily {
    pub ty_params: Vec<Ptr<TyParam>>,
    pub param_tys: Vec<SubstTy>,
    pub ret_ty: SubstTy,
    // TODO body
}
