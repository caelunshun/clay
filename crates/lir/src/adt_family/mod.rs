use crate::{
    adt_family::{enum_::EnumTyFamily, strukt::StructTyFamily},
    arena::Ptr,
    ty_param::TyParam,
};

pub mod enum_;
pub mod strukt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdtTyFamily {
    pub ty_params: Vec<Ptr<TyParam>>,
    pub kind: AdtKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdtKind {
    Struct(StructTyFamily),
    Enum(EnumTyFamily),
}
