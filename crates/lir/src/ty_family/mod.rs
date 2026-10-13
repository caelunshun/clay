use crate::{
    arena::Ptr,
    ty::{BufferTy, RefTy, SliceTy, prim::PrimTy},
    ty_family::{enum_::EnumTyFamily, strukt::StructTyFamily},
};

pub mod enum_;
pub mod strukt;

/// Defines a family of concrete types, parametrized over a set of zero or more type parameters.
///
/// Interned: each unique AbstractTy exists at most once in a soup's abstract_tys arena.
///
/// Some variants have no type parameters, so can be directly converted to concrete types.
/// Others require substitution.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TyFamily {
    /// Already concrete.
    Prim(PrimTy),
    /// Already concrete.
    Slice(SliceTy),
    /// Already concrete.
    Buffer(BufferTy),
    /// Already concrete.
    StrSlice,
    /// Already concrete.
    StrBuffer,
    /// Already concrete.
    Ref(RefTy),
    /// Can have type parameters.
    Adt(AdtTyFamily),
}

impl TyFamily {
    pub fn ty_params(&self) -> &[Ptr<TyParam>] {
        match self {
            TyFamily::Adt(adt) => &adt.ty_params,
            _ => &[],
        }
    }
}

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

#[derive(Debug, Clone)]
pub struct TyParam {}
