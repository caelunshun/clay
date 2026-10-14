use crate::ty::Ty;

#[derive(Debug, Clone)]
pub struct Sig {
    pub param_tys: Vec<Ty>,
    pub ret_ty: Ty,
}
