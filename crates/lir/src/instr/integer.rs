use crate::{func_family::val::ValPtr, instr, instr::CmpMode};

instr! {
    pub struct IntConstant {
        pub result: ValPtr<'g>,
        pub constant: i64 ,
    }
}

instr! {
    pub struct IntAdd {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct IntMul {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct IntSub {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct IntDiv {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct IntMod {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct IntSExt {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct IntZExt {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct IntTrunc {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct IntChangeSignedness {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct IntBitAnd {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct IntBitOr {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct IntBitXor {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct IntBitNot {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct IntNeg {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct IntCmp {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
        pub mode: CmpMode,
    }
}
