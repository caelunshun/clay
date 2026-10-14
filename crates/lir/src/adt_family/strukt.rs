use crate::{arena::Ptr, subst_ty::SubstTy};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructTyFamily {
    pub fields: Vec<Ptr<Field>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    pub ty: SubstTy,
}
