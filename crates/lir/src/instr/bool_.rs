use crate::{func_family::val::ValPtr, instr};

instr! {
    pub struct BoolConst {
        pub result: ValPtr<'g>,
        pub constant: bool,
    }
}

instr! {
    pub struct BoolAnd {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct BoolOr {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct BoolXor {
        pub result: ValPtr<'g>,
        pub lhs: ValPtr<'g>,
        pub rhs: ValPtr<'g>,
    }
}

instr! {
    pub struct BoolNot {
        pub result: ValPtr<'g>,
        pub operand: ValPtr<'g>,
    }
}
