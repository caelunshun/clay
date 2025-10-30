use crate::{
    ValId,
    ir::{BasicBlockId, Constant, FieldId, FuncInstance, Type},
};
use cranelift_entity::{EntityList, ListPool};

#[derive(Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub enum InstrData<'db> {
    Jump(Jump),
    Branch(Branch),
    Call(Call<'db>),
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

    InitStruct(InitStruct<'db>),
    GetField(GetField),
    SetField(SetField),
    Alloc(Alloc),
    Load(Load),
    Store(Store),
    MakeFieldMRef(MakeFieldMRef),

    MakeBufref(MakeBufref<'db>),
    BufrefPush(BufrefPush),
    BufrefRemove(BufrefRemove),
    BufrefTrunc(BufrefTrunc),
    BufrefLen(BufrefLen),
    BufrefGet(BufrefGet),
    BufregGetMRef(BufrefGetMRef),
}

impl InstrData<'_> {
    pub fn is_block_terminator(&self) -> bool {
        matches!(
            self,
            InstrData::Jump(_) | InstrData::Branch(_) | InstrData::Return(_)
        )
    }

    pub fn visit_successors(&self, mut visit: impl FnMut(BasicBlockId)) {
        match self {
            InstrData::Jump(ins) => visit(ins.target),
            InstrData::Branch(ins) => {
                visit(ins.target_true);
                visit(ins.target_false);
            }
            _ => {}
        }
    }

    pub fn visit_src_operands(&self, val_lists: &ListPool<ValId>, mut visit: impl FnMut(ValId)) {
        // TODO don't clone val_lists - keyword generics would make this easy but will never come :(
        let _ = self.map_src_operands(&mut val_lists.clone(), |val| {
            visit(val);
            val
        });
    }

    pub fn visit_dst_operands(&self, val_lists: &ListPool<ValId>, mut visit: impl FnMut(ValId)) {
        let _ = self.map_dst_operands(&mut val_lists.clone(), |val| {
            visit(val);
            val
        });
    }

    #[must_use]
    pub fn map_src_operands(
        &self,
        val_lists: &mut ListPool<ValId>,
        mut map: impl FnMut(ValId) -> ValId,
    ) -> Self {
        let mut this = self.clone();
        match &mut this {
            InstrData::Jump(_) => {}
            InstrData::Branch(ins) => ins.condition = map(ins.condition),
            InstrData::Call(ins) => {
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
            | InstrData::BoolNot(ins) => {
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
            InstrData::MakeFieldMRef(ins) => {
                ins.src_ref = map(ins.src_ref);
            }
            InstrData::MakeBufref(_) => {}
            InstrData::BufrefPush(ins) => {
                ins.src_bufref = map(ins.src_bufref);
                ins.src_element = map(ins.src_element);
            }
            InstrData::BufrefRemove(ins) => {
                ins.src_bufref = map(ins.src_bufref);
                ins.src_index = map(ins.src_index);
            }
            InstrData::BufrefTrunc(ins) => {
                ins.src_bufref = map(ins.src_bufref);
                ins.new_len = map(ins.new_len);
            }
            InstrData::BufrefLen(ins) => {
                ins.src_bufref = map(ins.src_bufref);
            }
            InstrData::BufrefGet(ins) => {
                ins.src_bufref = map(ins.src_bufref);
                ins.src_index = map(ins.src_index);
            }
            InstrData::BufregGetMRef(ins) => {
                ins.src_bufref = map(ins.src_bufref);
                ins.src_index = map(ins.src_index);
            }
        }
        this
    }

    #[must_use]
    pub fn map_dst_operands(
        &self,
        _val_lists: &mut ListPool<ValId>,
        mut map: impl FnMut(ValId) -> ValId,
    ) -> Self {
        let mut this = self.clone();
        match &mut this {
            InstrData::Jump(_) => {}
            InstrData::Branch(_) => {}
            InstrData::Call(ins) => {
                ins.return_value_dst = map(ins.return_value_dst);
            }
            InstrData::Return(_) => {}
            InstrData::Copy(ins)
            | InstrData::RealToInt(ins)
            | InstrData::IntToReal(ins)
            | InstrData::ByteToInt(ins)
            | InstrData::IntToByte(ins)
            | InstrData::BoolNot(ins) => {
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
            InstrData::MakeFieldMRef(ins) => {
                ins.dst_ref = map(ins.dst_ref);
            }
            InstrData::MakeBufref(ins) => {
                ins.dst = map(ins.dst);
            }
            InstrData::BufrefPush(ins) => {
                ins.dst_bufref = map(ins.dst_bufref);
            }
            InstrData::BufrefRemove(ins) => {
                ins.dst_bufref = map(ins.dst_bufref);
            }
            InstrData::BufrefTrunc(ins) => {
                ins.dst_bufref = map(ins.dst_bufref);
            }
            InstrData::BufrefLen(ins) => {
                ins.dst_len = map(ins.dst_len);
            }
            InstrData::BufrefGet(ins) => {
                ins.dst_val = map(ins.dst_val);
            }
            InstrData::BufregGetMRef(ins) => {
                ins.dst_ref = map(ins.dst_ref);
            }
        }
        this
    }

    #[must_use]
    pub fn move_to_list_pool(
        &self,
        old_pool: &ListPool<ValId>,
        new_pool: &mut ListPool<ValId>,
    ) -> Self {
        fn mv(
            list: &mut EntityList<ValId>,
            old_pool: &ListPool<ValId>,
            new_pool: &mut ListPool<ValId>,
        ) {
            *list = EntityList::from_slice(list.as_slice(old_pool), new_pool);
        }

        let mut this = self.clone();

        match &mut this {
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
            _ => {}
        }
        this
    }

    pub fn successor_args_mut(&mut self, successor: BasicBlockId) -> &mut EntityList<ValId> {
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
    pub target: BasicBlockId,
    /// Only used after SSA transformation; empty before then.
    pub args: EntityList<ValId>,
}

/// Conditional jump.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Branch {
    pub target_true: BasicBlockId,
    pub target_false: BasicBlockId,
    /// Only used after SSA transformation; empty before then.
    pub args_true: EntityList<ValId>,
    /// Only used after SSA transformation; empty before then.
    pub args_false: EntityList<ValId>,
    /// Must be of type `PrimitiveType::Bool`.
    pub condition: ValId,
}

/// Directly call a top-level function.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Call<'db> {
    /// Statically known function to call.
    /// It must have a unit captures type (i.e.
    /// be a top-level function).
    pub func: FuncInstance<'db>,
    /// Arguments to pass to the function.
    pub args: EntityList<ValId>,
    /// Destination for the return value.
    pub return_value_dst: ValId,
}

/// Return a value to the caller.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Return {
    pub return_value: ValId,
}

/// Copy a constant value into a local.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct ConstantInstr<'db> {
    pub dst: ValId,
    pub constant: Constant<'db>,
}

/// Instruction with two source operands
/// and one destination.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Binary {
    pub dst: ValId,
    pub src1: ValId,
    pub src2: ValId,
}

/// Instruction with one source operand
/// and one destination.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Unary {
    pub dst: ValId,
    pub src: ValId,
}

/// Comparison of two values, resulting in a boolean.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Cmp {
    pub dst: ValId,
    pub src1: ValId,
    pub src2: ValId,
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
#[derive(Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct InitStruct<'db> {
    pub dst: ValId,
    /// Type of struct to initialize.
    pub typ: Type<'db>,
    /// Field values to initialize, in the same
    /// order as the struct fields are declared.
    pub fields: EntityList<ValId>,
}

/// Copy a field in a local struct into its own local.
/// The struct should be a local, not a reference.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct GetField {
    pub dst: ValId,
    pub src_struct: ValId,
    pub field: FieldId,
}

/// Overwrite the value of a struct field, writing
/// the updated struct into `dst`. The struct should
/// be a local, not behind a reference.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct SetField {
    pub dst_struct: ValId,
    pub src_struct: ValId,
    pub src_field_val: ValId,
    pub field: FieldId,
}

/// Create a managed (garbage-collected / "heap"") object
/// from local ("stack") data.
///
/// Result type is Reference(typeof(src)).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Alloc {
    pub dst_ref: ValId,
    pub src: ValId,
}

/// Copy a value behind a reference (managed or ephemeral)
/// into a local.
///
/// Type of `src` must be `Reference(?T)`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Load {
    pub dst: ValId,
    pub src_ref: ValId,
}

/// Copy a local value into the memory pointed
/// to by the given reference. The reference can be
/// managed or ephemeral.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct Store {
    pub ref_: ValId,
    pub val: ValId,
}

/// Creates an MRef to a field of a struct,
/// given a reference to the struct.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct MakeFieldMRef {
    pub dst_ref: ValId,
    pub src_ref: ValId,
    pub field: FieldId,
}

/// Create an empty bufref.
#[derive(Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct MakeBufref<'db> {
    pub dst: ValId,
    /// Type of the elements inside the bufref.
    pub element_type: Type<'db>,
}

/// Append a value onto the end of a bufref.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct BufrefPush {
    pub dst_bufref: ValId,
    pub src_bufref: ValId,
    pub src_element: ValId,
}

/// Copy a value in a bufref to a local value.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct BufrefGet {
    pub dst_val: ValId,
    pub src_bufref: ValId,
    pub src_index: ValId,
}

/// Create an MRef to a value inside a bufref.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct BufrefGetMRef {
    pub dst_ref: ValId,
    pub src_bufref: ValId,
    pub src_index: ValId,
}

/// Get the length of a bufref, as an Int.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct BufrefLen {
    pub dst_len: ValId,
    pub src_bufref: ValId,
}

/// Removes an element from a bufref by its index, moving elements
/// from higher to lower indexes to fill the gap.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct BufrefRemove {
    pub dst_bufref: ValId,
    pub src_bufref: ValId,
    pub src_index: ValId,
}

/// Truncates a bufref to have the given updated size.
/// (Panics if the bufref length was less than the requested
/// new size.)
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub struct BufrefTrunc {
    pub dst_bufref: ValId,
    pub src_bufref: ValId,
    pub new_len: ValId,
}

/// A specified ordering for an atomic load.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub enum LoadOrdering {
    /// See LLVM's documentation on unordered atomics.
    /// They are roughly equivalent to Java's non-atomic
    /// loads and stores, in that there is no undefined behavior
    /// with concurrent mutation, but there are not many other guarantees.
    Unordered,
    /// LLVM's monotonic ordering.
    Relaxed,
    Acquire,
    SeqCst,
}

/// A specified ordering for an atomic store.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub enum StoreOrdering {
    /// See LLVM's documentation on unordered atomics.
    /// They are roughly equivalent to Java's non-atomic
    /// loads and stores, in that there is no undefined behavior
    /// with concurrent mutation, but there are not many other guarantees.
    Unordered,
    /// LLVM's monotonic ordering.
    Relaxed,
    Release,
    SeqCst,
}
