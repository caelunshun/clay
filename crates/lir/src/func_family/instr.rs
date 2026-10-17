use crate::{arena::Ptr, func_family::val::Val};

#[derive(Debug, Clone)]
pub enum Instr {
    // --- Integer arithmetic --- //
    // All operands must have the same bitness and signedness.
    IntAdd(Binary),
    IntSub(Binary),
    IntMul(Binary),
    IntDiv(Binary),
    IntAnd(Binary),
    IntOr(Binary),
    IntXor(Binary),
}

#[derive(Debug, Clone)]
pub struct Binary {
    pub dst: Ptr<Val>,
    pub lhs: Ptr<Val>,
    pub rhs: Ptr<Val>,
}
