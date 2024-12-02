use crate::{
    module::{Constant, Field, Instr, LocalFunc},
    Local, LocalType,
};
use cranelift_entity::EntityList;

/// Current goal is to keep this struct at a size
/// of 12 bytes. 8 bytes would be possible
/// if rustc used more optimal enum layouts.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(C)] // ensure size does not change with new rustc
pub enum InstrData {
    Jump(Jump),
    Branch(Branch),
    Call(Call),
    Return(Return),
    Copy(Copy),

    IntConstant(ConstantInstr),
    IntAdd(BinaryInstr),
    IntSub(BinaryInstr),
    IntMul(BinaryInstr),
    IntDiv(BinaryInstr),
    IntCmp(CmpInstr),

    RealConstant(ConstantInstr),
    RealAdd(BinaryInstr),
    RealSub(BinaryInstr),
    RealMul(BinaryInstr),
    RealDiv(BinaryInstr),
    RealCmp(CmpInstr),

    BoolConstant(ConstantInstr),
    BoolAnd(BinaryInstr),
    BoolOr(BinaryInstr),
    BoolXor(BinaryInstr),
    BoolNot(UnaryInstr),

    InitStruct(InitStruct),
    GetField(GetField),
    SetField(SetField),
    Alloc(Alloc),
    Load(Load),
    LoadField(LoadField),
    Store(Store),
    StoreField(StoreField),

    MakeFunctionObject(MakeFunctionObject),
}

impl InstrData {
    pub fn set_branch_target(&mut self, target: Instr) {
        match self {
            InstrData::Jump(instr) => instr.target = target,
            InstrData::Branch(instr) => instr.target = target,
            _ => panic!("not a branch"),
        }
    }
}

/// Copy from one local to another.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Copy {
    pub dst: Local,
    pub src: Local,
}

/// Unconditional jump to a different instruction.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Jump {
    pub target: Instr,
}

/// Jump to a different instruction if a boolean local
/// is true.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Branch {
    pub target: Instr,
    /// Must be of type `PrimitiveType::Bool`.
    pub condition: Local,
}

/// Apply a function.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Call {
    /// Local containing the function object to call.
    pub func: Local,
    /// Arguments to pass to the function.
    pub args: EntityList<Local>,
    /// Destination for the return value.
    pub return_value_dst: Local,
}

/// Return a value to the caller.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Return {
    pub return_value: Local,
}

/// Copy a constant value into a local.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstantInstr {
    pub dst: Local,
    pub constant: Constant,
}

/// Instruction with two source operands
/// and one destination.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BinaryInstr {
    pub dst: Local,
    pub src1: Local,
    pub src2: Local,
}

/// Instruction with one source operand
/// and one destination.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnaryInstr {
    pub dst: Local,
    pub src: Local,
}

/// Comparison of two values, resulting in a boolean.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct CmpInstr {
    pub dst: Local,
    pub src1: Local,
    pub src2: Local,
    pub mode: CompareMode,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CompareMode {
    Less,
    LessOrEqual,
    Greater,
    GreaterOrEqual,
    Equal,
    NotEqual,
}

/// Initialize a struct from its field values.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct InitStruct {
    pub dst: Local,
    /// Type of struct to initialize.
    pub typ: LocalType,
    /// Field values to initialize, in the same
    /// order as the struct fields are declared.
    pub fields: EntityList<Local>,
}

/// Copy a field in a local struct into its own local.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct GetField {
    pub dst: Local,
    pub src_struct: Local,
    pub field: Field,
}

/// Copy a local into a local struct field.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SetField {
    pub dst_struct: Local,
    pub src: Local,
    pub field: Field,
}

/// Create a managed (garbage-collected / "heap"") object
/// from local ("stack") data.
///
/// Result type is Reference(typeof(src)).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Alloc {
    pub dst_ref: Local,
    pub src: Local,
}

/// Copy a value behind a managed reference
/// into a local.
///
/// Type of `src` must be `Reference(?T)`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Load {
    pub dst: Local,
    pub src_ref: Local,
}

/// Copy a field of a struct into a local. The struct
/// is behind a managed reference.
///
/// Type of `src` must be `Reference(Struct(?T))`.
/// Type of `dst` is `typeof(field)`.
/// `field` must be a valid field of the struct `T`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct LoadField {
    pub dst: Local,
    pub src_ref: Local,
    pub field: Field,
}

/// Store a local into the memory behind a managed reference.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Store {
    pub dst_ref: Local,
    pub src_val: Local,
}

/// Store a local into a field of a struct. The struct is behind
/// a managed reference.
///
/// Type of `dst_ref` must be `Reference(Struct(?T))`.
/// Type of `src_val` must be `typeof(field)`.
/// `field` must be a valid field of the struct `T`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct StoreField {
    pub dst_ref: Local,
    pub src_val: Local,
    pub field: Field,
}

/// Construct a function object, given the function
/// implementation (as a `Func` id) and a value containing
/// the captures for the function (not behind a reference).
///
/// The captures must have
/// the same type as the `captures_type` field of the corresponding
/// `FuncData`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct MakeFunctionObject {
    pub dst: Local,
    pub func: LocalFunc,
    pub captures: Local,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn instr_size_12_bytes() {
        assert!(
            size_of::<InstrData>() <= 12,
            "size_of::<InstrData>() == {}",
            size_of::<InstrData>()
        );
        // Ensure Vec<InstrData> does not waste space with padding between
        // elements.
        assert!(
            align_of::<InstrData>() <= 4,
            "align_of::<InstrData>() == {}",
            align_of::<InstrData>()
        );
    }
}
