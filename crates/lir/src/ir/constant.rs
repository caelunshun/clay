use crate::ir::typ::{PrimType, TypeKind};
use compact_str::CompactString;
use std::{
    hash::{Hash, Hasher},
    mem,
};

#[salsa::interned(debug)]
pub struct Constant<'db> {
    #[returns(ref)]
    pub value: ConstantValue,
}

#[derive(Clone, Debug)]
pub enum ConstantValue {
    Int(i64),
    Real(f64),
    Bool(bool),
    Str(CompactString),
}

/// Special PartialEq that compares floats
/// with bitwise equality.
impl PartialEq for ConstantValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ConstantValue::Int(a), ConstantValue::Int(b)) => a == b,
            (ConstantValue::Real(a), ConstantValue::Real(b)) => a.to_bits() == b.to_bits(),
            (ConstantValue::Bool(a), ConstantValue::Bool(b)) => a == b,
            (ConstantValue::Str(a), ConstantValue::Str(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for ConstantValue {}

impl Hash for ConstantValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        mem::discriminant(self).hash(state);
        match self {
            ConstantValue::Int(x) => x.hash(state),
            ConstantValue::Real(x) => x.to_bits().hash(state),
            ConstantValue::Bool(x) => x.hash(state),
            ConstantValue::Str(x) => x.hash(state),
        }
    }
}

impl ConstantValue {
    pub fn typ(&self) -> TypeKind<'static> {
        match self {
            ConstantValue::Int(_) => TypeKind::Prim(PrimType::Int),
            ConstantValue::Real(_) => TypeKind::Prim(PrimType::Real),
            ConstantValue::Bool(_) => TypeKind::Prim(PrimType::Bool),
            ConstantValue::Str(_) => TypeKind::Prim(PrimType::Str),
        }
    }
}
