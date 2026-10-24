use crate::{func_family::val::ValPtr, instr, instr::CmpMode};

instr! {
    pub struct FloatConst {
        pub result: ValPtr<'g>,
        pub constant: f64,
    }
}

instr! {
    pub struct FloatAdd {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct FloatMul {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct FloatSub {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct FloatDiv  {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct FloatMulAdd {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
        pub acc: ValPtr<'g>,
    }
}

instr! {
    pub struct FloatNeg {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct FloatToBits {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct FloatFromBits {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct FloatToInt {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct FloatTruncFromInt {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct FloatConvert {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}

instr! {
    pub struct FloatCmp {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
        pub mode: CmpMode,
    }
}
