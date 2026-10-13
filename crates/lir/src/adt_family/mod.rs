use crate::adt_family::{enum_::EnumTyFamily, strukt::StructTyFamily};
use index_vec::IndexVec;

pub mod enum_;
pub mod strukt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AdtTyFamily {
    pub ty_params: IndexVec<TyParamIdx, TyParam>,
    pub kind: AdtKind,
}

index_vec::define_index_type! {
    pub struct TyParamIdx = u32;
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
