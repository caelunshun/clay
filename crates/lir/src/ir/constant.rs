use crate::{
    FloatBitness, IntBitness,
    ir::typ::{PrimType, TypeKind},
};
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
    SInt(i64, IntBitness),
    UInt(u64, IntBitness),
    Float(f64, FloatBitness),
    Bool(bool),
    Str(CompactString),
}

/// Special PartialEq that compares floats
/// with bitwise equality.
impl PartialEq for ConstantValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ConstantValue::SInt(a, a_bitness), ConstantValue::SInt(b, b_bitness)) => {
                a == b && a_bitness == b_bitness
            }
            (ConstantValue::UInt(a, a_bitness), ConstantValue::UInt(b, b_bitness)) => {
                a == b && a_bitness == b_bitness
            }
            (ConstantValue::Float(a, a_bitness), ConstantValue::Float(b, b_bitness)) => {
                a.to_bits() == b.to_bits() && a_bitness == b_bitness
            }
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
            ConstantValue::UInt(x, bitness) => (x, bitness).hash(state),
            ConstantValue::SInt(x, bitness) => (x, bitness).hash(state),
            ConstantValue::Float(x, bitness) => (x.to_bits(), bitness).hash(state),
            ConstantValue::Bool(x) => x.hash(state),
            ConstantValue::Str(x) => x.hash(state),
        }
    }
}

impl ConstantValue {
    pub fn typ(&self) -> TypeKind<'static> {
        match self {
            ConstantValue::SInt(_, bitness) => TypeKind::Prim(PrimType::SInt(*bitness)),
            ConstantValue::UInt(_, bitness) => TypeKind::Prim(PrimType::UInt(*bitness)),
            ConstantValue::Float(_, bitness) => TypeKind::Prim(PrimType::Float(*bitness)),
            ConstantValue::Bool(_) => TypeKind::Prim(PrimType::Bool),
            ConstantValue::Str(_) => TypeKind::Prim(PrimType::Str),
        }
    }
}
