use crate::subst_ty::SubstTy;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructTyFamily {
    pub fields: Vec<Field>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Field {
    pub ty: SubstTy,
}
