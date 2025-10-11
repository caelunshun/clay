use crate::{
    instr,
    instr::CompareMode,
    module::{
        bool_type, int_type, memoized_type, BasicBlock, BasicBlockData, Constant, Field, FuncData,
        ValData,
    },
    Func, InstrData, Type, TypeData, Val,
};
use compact_str::CompactString;
use cranelift_entity::{EntityList, ListPool, PrimaryMap};
use zyon_core::Db;

/// Builder API for a `FuncData`.
pub struct FuncBuilder<'db> {
    db: &'db Db,
    func: FuncData<'db>,
    current_block: BasicBlock,
}

impl<'db> FuncBuilder<'db> {
    pub fn new(
        db: &'db Db,
        name: impl Into<CompactString>,
        captures_type: Type<'db>,
        return_type: Type<'db>,
    ) -> Self {
        let mut basic_blocks = PrimaryMap::new();
        let entry_block = basic_blocks.push(BasicBlockData::default());
        let mut val_lists = ListPool::new();
        let mut vals = PrimaryMap::new();

        let captures_val = vals.push(ValData { typ: captures_type });
        basic_blocks[entry_block]
            .params
            .push(captures_val, &mut val_lists);

        Self {
            db,
            func: FuncData {
                name: name.into(),
                captures_type,
                vals,
                param_types: vec![],
                return_type,
                basic_blocks,
                entry_block,
                val_lists,
            },
            current_block: entry_block,
        }
    }

    pub fn append_param(&mut self, typ: Type<'db>) -> Val {
        let val = self.func.vals.push(ValData { typ });
        self.func.param_types.push(typ);
        self.func.basic_blocks[self.func.entry_block]
            .params
            .push(val, &mut self.func.val_lists);
        val
    }

    pub fn create_block(&mut self) -> BasicBlock {
        self.func.basic_blocks.push(BasicBlockData::default())
    }

    pub fn switch_to_block(&mut self, block: BasicBlock) {
        self.current_block = block;
    }

    pub fn instr<'a>(&'a mut self) -> FuncInstrBuilder<'a, 'db> {
        FuncInstrBuilder {
            db: self.db,
            func: &mut self.func,
            block: self.current_block,
        }
    }

    pub fn finish(self) -> FuncData<'db> {
        self.func
    }
}

pub struct FuncInstrBuilder<'a, 'db> {
    db: &'db Db,
    func: &'a mut FuncData<'db>,
    block: BasicBlock,
}

impl<'a, 'db> FuncInstrBuilder<'a, 'db> {
    pub fn jump(mut self, target: BasicBlock) {
        self.instr(InstrData::Jump(instr::Jump {
            target,
            args: EntityList::new(), // empty until SSA transformation
        }));
    }

    pub fn branch(mut self, condition: Val, target_true: BasicBlock, target_false: BasicBlock) {
        self.instr(InstrData::Branch(instr::Branch {
            target_true,
            target_false,
            args_true: EntityList::new(), // empty until SSA transformation
            args_false: EntityList::new(), // empty until SSA transformation
            condition,
        }));
    }

    pub fn call(
        mut self,
        return_value_dst: Val,
        func: Func<'db>,
        args: impl IntoIterator<Item = Val>,
    ) {
        let args = EntityList::from_iter(args, &mut self.func.val_lists);
        self.instr(InstrData::Call(instr::Call {
            func,
            args,
            return_value_dst,
        }));
    }

    pub fn call_indirect(
        mut self,
        return_value_dst: Val,
        func_object: Val,
        args: impl IntoIterator<Item = Val>,
    ) {
        let TypeData::Func(func) = self.func.vals[func_object].typ.data(self.db) else {
            panic!("call_indirect used on non-function type");
        };
        let args = EntityList::from_iter(args, &mut self.func.val_lists);
        self.instr(InstrData::CallIndirect(instr::CallIndirect {
            func: func_object,
            args,
            return_value_dst,
        }));
    }

    pub fn return_(mut self, return_value: Val) {
        self.instr(InstrData::Return(instr::Return { return_value }));
    }

    pub fn copy(mut self, dst: Val, src: Val) {
        self.instr(InstrData::Copy(instr::Unary { dst, src }));
    }

    pub fn constant(mut self, dst: Val, constant: Constant<'db>) {
        self.instr(InstrData::Constant(instr::ConstantInstr { dst, constant }));
    }

    pub fn int_add(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::IntAdd(instr::Binary { dst, src1, src2 }));
    }

    pub fn int_sub(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::IntSub(instr::Binary { dst, src1, src2 }));
    }

    pub fn int_mul(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::IntMul(instr::Binary { dst, src1, src2 }));
    }

    pub fn int_div(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::IntDiv(instr::Binary { dst, src1, src2 }));
    }

    pub fn int_cmp(mut self, dst: Val, src1: Val, src2: Val, mode: CompareMode) {
        self.instr(InstrData::IntCmp(instr::Cmp {
            dst,
            src1,
            src2,
            mode,
        }));
    }

    pub fn real_add(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::RealAdd(instr::Binary { dst, src1, src2 }));
    }

    pub fn real_sub(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::RealSub(instr::Binary { dst, src1, src2 }));
    }

    pub fn real_mul(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::RealMul(instr::Binary { dst, src1, src2 }));
    }

    pub fn real_div(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::RealDiv(instr::Binary { dst, src1, src2 }));
    }

    pub fn real_cmp(mut self, dst: Val, src1: Val, src2: Val, mode: CompareMode) {
        self.instr(InstrData::RealCmp(instr::Cmp {
            dst,
            src1,
            src2,
            mode,
        }));
    }

    pub fn real_to_int(mut self, dst: Val, src: Val) {
        self.instr(InstrData::RealToInt(instr::Unary { dst, src }));
    }

    pub fn int_to_real(mut self, dst: Val, src: Val) {
        self.instr(InstrData::IntToReal(instr::Unary { dst, src }));
    }

    pub fn byte_to_int(mut self, dst: Val, src: Val) {
        self.instr(InstrData::ByteToInt(instr::Unary { dst, src }));
    }

    pub fn int_to_byte(mut self, dst: Val, src: Val) {
        self.instr(InstrData::IntToByte(instr::Unary { dst, src }));
    }

    pub fn bool_and(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::BoolAnd(instr::Binary { dst, src1, src2 }));
    }

    pub fn bool_or(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::BoolOr(instr::Binary { dst, src1, src2 }));
    }

    pub fn bool_xor(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::BoolXor(instr::Binary { dst, src1, src2 }));
    }

    pub fn bool_not(mut self, dst: Val, src: Val) {
        self.instr(InstrData::BoolNot(instr::Unary { dst, src }));
    }

    pub fn local_to_eref(mut self, dst: Val, src: Val) {
        self.instr(InstrData::LocalToERef(instr::Unary { dst, src }));
    }

    pub fn init_struct(
        mut self,
        dst: Val,
        struct_type: Type<'db>,
        field_values: impl IntoIterator<Item = Val>,
    ) {
        let fields = EntityList::from_iter(field_values, &mut self.func.val_lists);
        self.instr(InstrData::InitStruct(instr::InitStruct {
            dst,
            typ: struct_type,
            fields,
        }));
    }

    pub fn get_field(mut self, dst: Val, src: Val, field: Field) {
        self.instr(InstrData::GetField(instr::GetField {
            dst,
            src_struct: src,
            field,
        }));
    }

    pub fn set_field(mut self, dst: Val, src_struct: Val, src_field_val: Val, field: Field) {
        self.instr(InstrData::SetField(instr::SetField {
            dst_struct: dst,
            src_struct,
            src_field_val,
            field,
        }));
    }

    pub fn alloc(mut self, dst: Val, src: Val) {
        self.instr(InstrData::Alloc(instr::Alloc { dst_ref: dst, src }));
    }

    pub fn load(mut self, dst: Val, src_ref: Val) {
        self.instr(InstrData::Load(instr::Load { dst, src_ref }));
    }

    pub fn store(mut self, ref_: Val, val: Val) {
        self.instr(InstrData::Store(instr::Store { ref_, val }));
    }

    pub fn make_field_eref(mut self, dst: Val, src: Val, field: Field) {
        self.instr(InstrData::MakeFieldERef(instr::MakeFieldERef {
            dst_ref: dst,
            src_ref: src,
            field,
        }));
    }

    pub fn make_function_object(mut self, dst: Val, func: Func<'db>, captures_ref: Val) {
        self.instr(InstrData::MakeFunctionObject(instr::MakeFunctionObject {
            dst,
            func,
            captures_ref,
        }));
    }

    pub fn make_list(mut self, dst: Val, element_type: Type<'db>) {
        self.instr(InstrData::MakeList(instr::MakeList { dst, element_type }));
    }

    pub fn list_push(mut self, dst: Val, src_list: Val, src_element: Val) {
        self.instr(InstrData::ListPush(instr::ListPush {
            dst_list: Some(dst),
            src_list,
            src_element,
        }));
    }

    pub fn list_ref_push(mut self, src_list: Val, src_element: Val) {
        self.instr(InstrData::ListPush(instr::ListPush {
            dst_list: None,
            src_list,
            src_element,
        }));
    }

    pub fn list_remove(mut self, dst: Val, src_list: Val, src_index: Val) {
        self.instr(InstrData::ListRemove(instr::ListRemove {
            dst_list: Some(dst),
            src_list,
            src_index,
        }));
    }

    pub fn list_ref_remove(mut self, src_list: Val, src_index: Val) {
        self.instr(InstrData::ListRemove(instr::ListRemove {
            dst_list: None,
            src_list,
            src_index,
        }));
    }

    pub fn list_trunc(mut self, dst: Val, src_list: Val, new_len: Val) {
        self.instr(InstrData::ListTrunc(instr::ListTrunc {
            dst_list: Some(dst),
            src_list,
            new_len,
        }));
    }

    pub fn list_ref_trunc(mut self, src_list: Val, new_len: Val) {
        self.instr(InstrData::ListTrunc(instr::ListTrunc {
            dst_list: None,
            src_list,
            new_len,
        }));
    }

    pub fn list_len(mut self, dst: Val, src: Val) {
        self.instr(InstrData::ListLen(instr::ListLen {
            dst_len: dst,
            src_list: src,
        }));
    }

    pub fn list_get(mut self, dst: Val, src_list: Val, src_index: Val) {
        self.instr(InstrData::ListGet(instr::ListGet {
            dst_val: dst,
            src_list,
            src_index,
        }));
    }

    pub fn list_get_eref(mut self, dst: Val, src_list: Val, src_index: Val) {
        self.instr(InstrData::ListGetERef(instr::ListGetERef {
            dst_ref: dst,
            src_list,
            src_index,
        }));
    }

    fn instr(&mut self, instr: InstrData<'db>) {
        self.func.basic_blocks[self.block].instrs.push(instr);
    }
}
