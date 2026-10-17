use crate::subst_ty::SubstTy;

#[derive(Debug, Clone)]
pub struct Val {
    pub ty: SubstTy,
}
