use crate::{
    adt_family::{enum_::EnumTyFamily, strukt::StructTyFamily},
    arena::Ptr,
};

pub mod enum_;
pub mod strukt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AdtTyFamily {
    pub ty_params: Vec<Ptr<TyParam>>,
    pub kind: AdtKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AdtKind {
    Struct(StructTyFamily),
    Enum(EnumTyFamily),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TyParam {}

impl TyParam {
    pub fn unconstrained() -> Self {
        Self {}
    }
}
