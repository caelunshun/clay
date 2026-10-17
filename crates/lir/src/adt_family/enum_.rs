use crate::{arena::Ptr, subst_ty::SubstTy};

#[derive(Debug, Clone)]
pub struct EnumTyFamily {
    pub variants: Vec<Ptr<Variant>>,
}

#[derive(Debug, Clone)]
pub struct Variant {
    pub contents: SubstTy,
}
