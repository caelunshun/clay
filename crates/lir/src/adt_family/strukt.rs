use crate::{arena::Ptr, subst_ty::SubstTy};

#[derive(Debug, Clone)]
pub struct StructTyFamily {
    pub fields: Vec<Ptr<Field>>,
}

#[derive(Debug, Clone)]
pub struct Field {
    pub ty: SubstTy,
}
