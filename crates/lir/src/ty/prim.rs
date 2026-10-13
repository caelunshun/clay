#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum PrimTy {
    Unit,
    Bool,
    Int(IntTy),
    Float(FloatTy),
    StrSlice,
    StrBuffer,
    Never,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct IntTy {
    pub bitness: IntBitness,
    pub signedness: IntSignedness,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum IntSignedness {
    Signed,
    Unsigned,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum IntBitness {
    B8,
    B16,
    B32,
    B64,
    B128,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum FloatTy {
    F32,
    F64,
}
