use crate::{
    Val,
    module::{BasicBlock, Constant, Field, FuncRef, TypeRef},
};
use cranelift_entity::{EntityList, ListPool};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub enum InstrData<'db> {
    Jump(Jump),
    Branch(Branch),
    Call(Call),
    CallIndirect(CallIndirect),
    Return(Return),
    Copy(Unary),

    Constant(ConstantInstr<'db>),

    IntAdd(Binary),
    IntSub(Binary),
    IntMul(Binary),
    IntDiv(Binary),
    IntCmp(Cmp),

    RealAdd(Binary),
    RealSub(Binary),
    RealMul(Binary),
    RealDiv(Binary),
    RealCmp(Cmp),

    /// Float to signed integer conversion with saturation.
    /// NaN maps to 0.
    RealToInt(Unary),
    /// Signed integer to float conversion, rounding to nearest.
    IntToReal(Unary),

    ByteToInt(Unary),
    /// Truncating conversion from 64-bit integer to byte.
    IntToByte(Unary),

    BoolAnd(Binary),
    BoolOr(Binary),
    BoolXor(Binary),
    BoolNot(Unary),

    /// Promote a local value to an ERef.
    /// This can be viewed as executing the following steps:
    /// (1) Allocate a stack slot for the local
    /// (2) Copy the value into the stack slot
    /// (3) Yield a reference to the stack slot
    ///
    /// Since this logically creates a copy, the original
    /// local is not referenced.
    LocalToERef(Unary),

    InitStruct(InitStruct),
    GetField(GetField),
    SetField(SetField),
    Alloc(Alloc),
    Load(Load),
    Store(Store),
    MakeFieldERef(MakeFieldERef),

    MakeFunctionObject(MakeFunctionObject),

    MakeList(MakeList),
    ListPush(ListPush),
    ListRemove(ListRemove),
    ListTrunc(ListTrunc),
    ListLen(ListLen),
    ListGet(ListGet),
    ListGetERef(ListGetERef),
}

impl InstrData<'_> {
    pub fn is_block_terminator(&self) -> bool {
        matches!(
            self,
            InstrData::Jump(_) | InstrData::Branch(_) | InstrData::Return(_)
        )
    }

    pub fn visit_successors(self, mut visit: impl FnMut(BasicBlock)) {
        match self {
            InstrData::Jump(ins) => visit(ins.target),
            InstrData::Branch(ins) => {
                visit(ins.target_true);
                visit(ins.target_false);
            }
            _ => {}
        }
    }

    pub fn visit_src_operands(self, val_lists: &ListPool<Val>, mut visit: impl FnMut(Val)) {
        // TODO don't clone val_lists - keyword generics would make this easy but will never come :(
        let _ = self.map_src_operands(&mut val_lists.clone(), |val| {
            visit(val);
            val
        });
    }

    pub fn visit_dst_operands(self, val_lists: &ListPool<Val>, mut visit: impl FnMut(Val)) {
        let _ = self.map_dst_operands(&mut val_lists.clone(), |val| {
            visit(val);
            val
        });
    }

    #[must_use]
    pub fn map_src_operands(
        mut self,
        val_lists: &mut ListPool<Val>,
        mut map: impl FnMut(Val) -> Val,
    ) -> Self {
        match &mut self {
            InstrData::Jump(_) => {}
            InstrData::Branch(ins) => ins.condition = map(ins.condition),
            InstrData::Call(ins) => {
                for arg in ins.args.as_mut_slice(val_lists) {
                    *arg = map(*arg);
                }
            }
            InstrData::CallIndirect(ins) => {
                ins.func = map(ins.func);
                for arg in ins.args.as_mut_slice(val_lists) {
                    *arg = map(*arg);
                }
            }
            InstrData::Return(ins) => {
                ins.return_value = map(ins.return_value);
            }
            InstrData::Copy(ins)
            | InstrData::RealToInt(ins)
            | InstrData::IntToReal(ins)
            | InstrData::ByteToInt(ins)
            | InstrData::IntToByte(ins)
            | InstrData::BoolNot(ins)
            | InstrData::LocalToERef(ins) => {
                ins.src = map(ins.src);
            }
            InstrData::Constant(_) => {}
            InstrData::IntAdd(ins)
            | InstrData::IntSub(ins)
            | InstrData::IntMul(ins)
            | InstrData::IntDiv(ins)
            | InstrData::RealAdd(ins)
            | InstrData::RealSub(ins)
            | InstrData::RealMul(ins)
            | InstrData::RealDiv(ins)
            | InstrData::BoolAnd(ins)
            | InstrData::BoolOr(ins)
            | InstrData::BoolXor(ins) => {
                ins.src1 = map(ins.src1);
                ins.src2 = map(ins.src2);
            }
            InstrData::IntCmp(ins) | InstrData::RealCmp(ins) => {
                ins.src1 = map(ins.src1);
                ins.src2 = map(ins.src2);
            }
            InstrData::InitStruct(ins) => {
                for field_val in ins.fields.as_mut_slice(val_lists) {
                    *field_val = map(*field_val);
                }
            }
            InstrData::GetField(ins) => {
                ins.src_struct = map(ins.src_struct);
            }
            InstrData::SetField(ins) => {
                ins.src_struct = map(ins.src_struct);
                ins.src_field_val = map(ins.src_field_val);
            }
            InstrData::Alloc(ins) => {
                ins.src = map(ins.src);
            }
            InstrData::Load(ins) => {
                ins.src_ref = map(ins.src_ref);
            }
            InstrData::Store(ins) => {
                ins.val = map(ins.val);
                ins.ref_ = map(ins.ref_);
            }
            InstrData::MakeFieldERef(ins) => {
                ins.src_ref = map(ins.src_ref);
            }
            InstrData::MakeFunctionObject(ins) => {
                ins.captures_ref = map(ins.captures_ref);
            }
            InstrData::MakeList(_) => {}
            InstrData::ListPush(ins) => {
                ins.src_list = map(ins.src_list);
                ins.src_element = map(ins.src_element);
            }
            InstrData::ListRemove(ins) => {
                ins.src_list = map(ins.src_list);
                ins.src_index = map(ins.src_index);
            }
            InstrData::ListTrunc(ins) => {
                ins.src_list = map(ins.src_list);
                ins.new_len = map(ins.new_len);
            }
            InstrData::ListLen(ins) => {
                ins.src_list = map(ins.src_list);
            }
            InstrData::ListGet(ins) => {
                ins.src_list = map(ins.src_list);
                ins.src_index = map(ins.src_index);
            }
            InstrData::ListGetERef(ins) => {
                ins.src_list = map(ins.src_list);
                ins.src_index = map(ins.src_index);
            }
        }
        self
    }

    #[must_use]
    pub fn map_dst_operands(
        mut self,
        _val_lists: &mut ListPool<Val>,
        mut map: impl FnMut(Val) -> Val,
    ) -> Self {
        match &mut self {
            InstrData::Jump(_) => {}
            InstrData::Branch(_) => {}
            InstrData::Call(ins) => {
                ins.return_value_dst = map(ins.return_value_dst);
            }
            InstrData::CallIndirect(ins) => {
                ins.return_value_dst = map(ins.return_value_dst);
            }
            InstrData::Return(_) => {}
            InstrData::Copy(ins)
            | InstrData::RealToInt(ins)
            | InstrData::IntToReal(ins)
            | InstrData::ByteToInt(ins)
            | InstrData::IntToByte(ins)
            | InstrData::BoolNot(ins)
            | InstrData::LocalToERef(ins) => {
                ins.dst = map(ins.dst);
            }
            InstrData::Constant(ins) => {
                ins.dst = map(ins.dst);
            }
            InstrData::IntAdd(ins)
            | InstrData::IntSub(ins)
            | InstrData::IntMul(ins)
            | InstrData::IntDiv(ins)
            | InstrData::RealAdd(ins)
            | InstrData::RealSub(ins)
            | InstrData::RealMul(ins)
            | InstrData::RealDiv(ins)
            | InstrData::BoolAnd(ins)
            | InstrData::BoolOr(ins)
            | InstrData::BoolXor(ins) => {
                ins.dst = map(ins.dst);
            }
            InstrData::IntCmp(ins) | InstrData::RealCmp(ins) => {
                ins.dst = map(ins.dst);
            }
            InstrData::InitStruct(ins) => {
                ins.dst = map(ins.dst);
            }
            InstrData::GetField(ins) => {
                ins.dst = map(ins.dst);
            }
            InstrData::SetField(ins) => {
                ins.dst_struct = map(ins.dst_struct);
            }
            InstrData::Alloc(ins) => {
                ins.dst_ref = map(ins.dst_ref);
            }
            InstrData::Load(ins) => {
                ins.dst = map(ins.dst);
            }
            InstrData::Store(_) => {}
            InstrData::MakeFieldERef(ins) => {
                ins.dst_ref = map(ins.dst_ref);
            }
            InstrData::MakeFunctionObject(ins) => {
                ins.dst = map(ins.dst);
            }
            InstrData::MakeList(ins) => {
                ins.dst = map(ins.dst);
            }
            InstrData::ListPush(ins) => {
                if let Some(dst_list) = &mut ins.dst_list {
                    *dst_list = map(*dst_list);
                }
            }
            InstrData::ListRemove(ins) => {
                if let Some(dst_list) = &mut ins.dst_list {
                    *dst_list = map(*dst_list);
                }
            }
            InstrData::ListTrunc(ins) => {
                if let Some(dst_list) = &mut ins.dst_list {
                    *dst_list = map(*dst_list);
                }
            }
            InstrData::ListLen(ins) => {
                ins.dst_len = map(ins.dst_len);
            }
            InstrData::ListGet(ins) => {
                ins.dst_val = map(ins.dst_val);
            }
            InstrData::ListGetERef(ins) => {
                ins.dst_ref = map(ins.dst_ref);
            }
        }
        self
    }

    #[must_use]
    pub fn move_to_list_pool(
        mut self,
        old_pool: &ListPool<Val>,
        new_pool: &mut ListPool<Val>,
    ) -> Self {
        fn mv(list: &mut EntityList<Val>, old_pool: &ListPool<Val>, new_pool: &mut ListPool<Val>) {
            *list = EntityList::from_slice(list.as_slice(old_pool), new_pool);
        }

        match &mut self {
            InstrData::Jump(j) => {
                mv(&mut j.args, old_pool, new_pool);
            }
            InstrData::Branch(b) => {
                mv(&mut b.args_false, old_pool, new_pool);
                mv(&mut b.args_true, old_pool, new_pool);
            }
            InstrData::InitStruct(ins) => {
                mv(&mut ins.fields, old_pool, new_pool);
            }
            InstrData::Call(ins) => {
                mv(&mut ins.args, old_pool, new_pool);
            }
            InstrData::CallIndirect(ins) => {
                mv(&mut ins.args, old_pool, new_pool);
            }
            _ => {}
        }
        self
    }

    pub fn successor_args_mut(&mut self, successor: BasicBlock) -> &mut EntityList<Val> {
        match self {
            InstrData::Jump(j) => {
                if j.target == successor {
                    &mut j.args
                } else {
                    panic!("not the successor")
                }
            }
            InstrData::Branch(b) => {
                if b.target_true == successor {
                    &mut b.args_true
                } else if b.target_false == successor {
                    &mut b.args_false
                } else {
                    panic!("not a successor")
                }
            }
            _ => panic!("successor_args_mut: not a terminator instruction"),
        }
    }
}

/// Unconditional jump to a basic block.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Jump {
    pub target: BasicBlock,
    /// Only used after SSA transformation; empty before then.
    pub args: EntityList<Val>,
}

/// Conditional jump.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Branch {
    pub target_true: BasicBlock,
    pub target_false: BasicBlock,
    /// Only used after SSA transformation; empty before then.
    pub args_true: EntityList<Val>,
    /// Only used after SSA transformation; empty before then.
    pub args_false: EntityList<Val>,
    /// Must be of type `PrimitiveType::Bool`.
    pub condition: Val,
}

/// Directly call a top-level function.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Call {
    /// Statically known function to call.
    /// It must have a unit captures type (i.e.
    /// be a top-level function).
    pub func: FuncRef,
    /// Arguments to pass to the function.
    pub args: EntityList<Val>,
    /// Destination for the return value.
    pub return_value_dst: Val,
}

/// Indirectly call a function object.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct CallIndirect {
    /// Function object to call.
    pub func: Val,
    /// Arguments to pass to the function.
    pub args: EntityList<Val>,
    /// Destination for the return value.
    pub return_value_dst: Val,
}

/// Return a value to the caller.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Return {
    pub return_value: Val,
}

/// Copy a constant value into a local.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct ConstantInstr<'db> {
    pub dst: Val,
    pub constant: Constant<'db>,
}

/// Instruction with two source operands
/// and one destination.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Binary {
    pub dst: Val,
    pub src1: Val,
    pub src2: Val,
}

/// Instruction with one source operand
/// and one destination.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Unary {
    pub dst: Val,
    pub src: Val,
}

/// Comparison of two values, resulting in a boolean.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Cmp {
    pub dst: Val,
    pub src1: Val,
    pub src2: Val,
    pub mode: CompareMode,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub enum CompareMode {
    Less,
    LessOrEqual,
    Greater,
    GreaterOrEqual,
    Equal,
    NotEqual,
}

/// Initialize a struct from its field values,
/// by copying each field into the new struct.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct InitStruct {
    pub dst: Val,
    /// Type of struct to initialize.
    pub typ: TypeRef,
    /// Field values to initialize, in the same
    /// order as the struct fields are declared.
    pub fields: EntityList<Val>,
}

/// Copy a field in a local struct into its own local.
/// The struct should be a local, not a reference.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct GetField {
    pub dst: Val,
    pub src_struct: Val,
    pub field: Field,
}

/// Overwrite the value of a struct field, writing
/// the updated struct into `dst`. The struct should
/// be a local, not behind a reference.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct SetField {
    pub dst_struct: Val,
    pub src_struct: Val,
    pub src_field_val: Val,
    pub field: Field,
}

/// Create a managed (garbage-collected / "heap"") object
/// from local ("stack") data.
///
/// Result type is Reference(typeof(src)).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Alloc {
    pub dst_ref: Val,
    pub src: Val,
}

/// Copy a value behind a reference (managed or ephemeral)
/// into a local.
///
/// Type of `src` must be `Reference(?T)`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Load {
    pub dst: Val,
    pub src_ref: Val,
}

/// Copy a local value into the memory pointed
/// to by the given reference. The reference can be
/// managed or ephemeral.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Store {
    pub ref_: Val,
    pub val: Val,
}

/// Creates an ERef to a field of a struct,
/// given a reference to the struct.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct MakeFieldERef {
    pub dst_ref: Val,
    pub src_ref: Val,
    pub field: Field,
}

/// Construct a function object, given the function
/// implementation (as a `Func` id) and a value containing
/// a reference to the captures for the function.
///
/// The captures must have
/// the same type as the `captures_type` field of the corresponding
/// `FuncData`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct MakeFunctionObject {
    pub dst: Val,
    pub func: FuncRef,
    pub captures_ref: Val,
}

/// Create an empty list.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct MakeList {
    pub dst: Val,
    /// Type of the elements inside the list.
    pub element_type: TypeRef,
}

// -------------------
// Instructions that work with lists can support either local
// (value) lists or lists behind a reference.
//
// For instructions that modify lists, the list is updated according
// to these rules:
// * For local lists, the updated list is placed in the `dst_list` value
// of the instruction, which must be `Some(_)`. The old list is not modified,
// to allow adherence to SSA.
// * For referenced lists, the list is directly mutated in memory,
// and the `dst_list` value of the instruction must be `None`.
// -------------------

/// Append a value onto the end of a list.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct ListPush {
    pub dst_list: Option<Val>,
    pub src_list: Val,
    pub src_element: Val,
}

/// Copy a value in a list to a local value.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct ListGet {
    pub dst_val: Val,
    pub src_list: Val,
    pub src_index: Val,
}

/// Create an ERef to a value inside a list.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct ListGetERef {
    pub dst_ref: Val,
    pub src_list: Val,
    pub src_index: Val,
}

/// Get the length of a list, as an Int.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct ListLen {
    pub dst_len: Val,
    pub src_list: Val,
}

/// Removes an element from a list by its index, moving elements
/// from higher to lower indexes to fill the gap.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct ListRemove {
    pub dst_list: Option<Val>,
    pub src_list: Val,
    pub src_index: Val,
}

/// Truncates a list to have the given updated size.
/// (Panics if the list length was less than the requested
/// new size.)
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct ListTrunc {
    pub dst_list: Option<Val>,
    pub src_list: Val,
    pub new_len: Val,
}
