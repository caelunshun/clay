use crate::{
    instr::{self, CompareMode},
    module::{
        BasicBlock, BasicBlockData, Constant, ContextBuilder, Field, FuncData, FuncHeader, FuncRef,
        FuncTypeData, TypeRef, ValData,
    },
    InstrData, TypeKind, Val,
};
use compact_str::CompactString;
use cranelift_entity::{EntityList, ListPool, PrimaryMap};
use salsa::Database;

/// Builder API for a `FuncData`.
pub struct FuncBuilder<'db> {
    db: &'db dyn Database,
    func: FuncData<'db>,
    current_block: BasicBlock,
    /// Values created so far.
    /// Some value types may not yet be resolved.
    val_types: PrimaryMap<Val, Option<TypeRef>>,
}

impl<'db> FuncBuilder<'db> {
    pub fn new(
        db: &'db dyn Database,
        name: impl Into<CompactString>,
        captures_type: TypeRef,
        return_type: TypeRef,
        cx: &mut ContextBuilder<'db>,
    ) -> Self {
        let mut basic_blocks = PrimaryMap::new();
        let entry_block = basic_blocks.push(BasicBlockData::default());
        let mut val_lists = ListPool::new();
        let mut val_types = PrimaryMap::new();

        let captures_val = val_types.push(Some(
            cx.get_or_create_type_ref_with_data(db, TypeKind::MRef(captures_type)),
        ));
        basic_blocks[entry_block]
            .params
            .push(captures_val, &mut val_lists);

        Self {
            db,
            func: FuncData {
                header: FuncHeader {
                    param_types: vec![],
                    return_type,
                    name: name.into(),
                    captures_type,
                },

                vals: PrimaryMap::default(),

                basic_blocks,
                entry_block,
                val_lists,
            },
            current_block: entry_block,
            val_types,
        }
    }

    pub fn append_param(&mut self, typ: TypeRef) -> Val {
        let val = self.val();
        self.val_types[val] = Some(typ);
        self.func.header.param_types.push(typ);
        self.func.basic_blocks[self.func.entry_block]
            .params
            .push(val, &mut self.func.val_lists);
        val
    }

    pub fn append_block_param(&mut self, typ: TypeRef) -> Val {
        let val = self.val();
        self.val_types[val] = Some(typ);
        self.func.basic_blocks[self.current_block]
            .params
            .push(val, &mut self.func.val_lists);
        val
    }

    pub fn create_block(&mut self) -> BasicBlock {
        self.func.basic_blocks.push(BasicBlockData::default())
    }

    pub fn entry_block(&self) -> BasicBlock {
        self.func.entry_block
    }

    pub fn block_param(&self, i: usize) -> Val {
        self.func.basic_blocks[self.current_block]
            .params
            .get(i, &self.func.val_lists)
            .unwrap()
    }

    pub fn switch_to_block(&mut self, block: BasicBlock) {
        self.current_block = block;
    }

    /// Creates a new value. Its type is not yet
    /// known; it is set when the value is first used
    /// as a destination operand.
    pub fn val(&mut self) -> Val {
        self.val_types.push(None)
    }

    pub fn instr<'b>(&'b mut self, cx: &'b mut ContextBuilder<'db>) -> FuncInstrBuilder<'b, 'db> {
        FuncInstrBuilder {
            db: self.db,
            func: &mut self.func,
            block: self.current_block,
            val_types: &mut self.val_types,
            cx,
        }
    }

    pub fn build(mut self, cx: &mut ContextBuilder<'db>) -> FuncData<'db> {
        // Resolve final value types
        for (val, val_type) in self.val_types {
            // If value type was never resolved
            // then the value is unused - any type is
            // valid - use unit type
            let val_type = val_type.unwrap_or_else(|| cx.unit_type_ref());
            // Same ID should be allocated since
            // same order of insertion into PrimaryMap
            assert_eq!(val, self.func.vals.push(ValData { typ: val_type }));
        }

        self.func
    }
}

pub struct FuncInstrBuilder<'a, 'db> {
    #[allow(unused)]
    db: &'db dyn Database,
    cx: &'a mut ContextBuilder<'db>,
    func: &'a mut FuncData<'db>,
    block: BasicBlock,
    val_types: &'a mut PrimaryMap<Val, Option<TypeRef>>,
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
        func: FuncRef,
        args: impl IntoIterator<Item = Val>,
    ) {
        let args = EntityList::from_iter(args, &mut self.func.val_lists);
        self.instr(InstrData::Call(instr::Call {
            func,
            args,
            return_value_dst,
        }));
        self.set_val_type(
            return_value_dst,
            func.resolve_header(self.db, self.cx).return_type,
        );
    }

    pub fn call_indirect(
        mut self,
        return_value_dst: Val,
        func_object: Val,
        args: impl IntoIterator<Item = Val>,
    ) {
        let args = EntityList::from_iter(args, &mut self.func.val_lists);
        self.instr(InstrData::CallIndirect(instr::CallIndirect {
            func: func_object,
            args,
            return_value_dst,
        }));
        let TypeKind::Func(func) = self.val_types[func_object]
            .unwrap()
            .resolve_in_builder(self.cx)
            .data(self.db)
        else {
            panic!("not a func")
        };
        self.set_val_type(return_value_dst, func.return_type);
    }

    pub fn return_(mut self, return_value: Val) {
        self.instr(InstrData::Return(instr::Return { return_value }));
    }

    pub fn copy(mut self, dst: Val, src: Val) {
        self.instr(InstrData::Copy(instr::Unary { dst, src }));
        self.set_val_type(dst, self.val_types[src].unwrap());
    }

    pub fn constant(mut self, dst: Val, constant: Constant<'db>) {
        self.instr(InstrData::Constant(instr::ConstantInstr { dst, constant }));
        let typ = TypeRef::create(self.db, constant.data(self.db).typ(), self.cx);
        self.set_val_type(dst, typ)
    }

    pub fn int_add(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::IntAdd(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, self.cx.int_type_ref());
    }

    pub fn int_sub(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::IntSub(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, self.cx.int_type_ref());
    }

    pub fn int_mul(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::IntMul(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, self.cx.int_type_ref());
    }

    pub fn int_div(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::IntDiv(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, self.cx.int_type_ref());
    }

    pub fn int_cmp(mut self, dst: Val, src1: Val, src2: Val, mode: CompareMode) {
        self.instr(InstrData::IntCmp(instr::Cmp {
            dst,
            src1,
            src2,
            mode,
        }));
        self.set_val_type(dst, self.cx.bool_type_ref());
    }

    pub fn real_add(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::RealAdd(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, self.cx.real_type_ref());
    }

    pub fn real_sub(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::RealSub(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, self.cx.real_type_ref());
    }

    pub fn real_mul(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::RealMul(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, self.cx.real_type_ref());
    }

    pub fn real_div(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::RealDiv(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, self.cx.real_type_ref());
    }

    pub fn real_cmp(mut self, dst: Val, src1: Val, src2: Val, mode: CompareMode) {
        self.instr(InstrData::RealCmp(instr::Cmp {
            dst,
            src1,
            src2,
            mode,
        }));
        self.set_val_type(dst, self.cx.bool_type_ref());
    }

    pub fn real_to_int(mut self, dst: Val, src: Val) {
        self.instr(InstrData::RealToInt(instr::Unary { dst, src }));
        self.set_val_type(dst, self.cx.int_type_ref());
    }

    pub fn int_to_real(mut self, dst: Val, src: Val) {
        self.instr(InstrData::IntToReal(instr::Unary { dst, src }));
        self.set_val_type(dst, self.cx.real_type_ref());
    }

    pub fn byte_to_int(mut self, dst: Val, src: Val) {
        self.instr(InstrData::ByteToInt(instr::Unary { dst, src }));
        self.set_val_type(dst, self.cx.int_type_ref());
    }

    pub fn int_to_byte(mut self, dst: Val, src: Val) {
        self.instr(InstrData::IntToByte(instr::Unary { dst, src }));
        self.set_val_type(dst, self.cx.byte_type_ref());
    }

    pub fn bool_and(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::BoolAnd(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, self.cx.bool_type_ref());
    }

    pub fn bool_or(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::BoolOr(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, self.cx.bool_type_ref());
    }

    pub fn bool_xor(mut self, dst: Val, src1: Val, src2: Val) {
        self.instr(InstrData::BoolXor(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, self.cx.bool_type_ref());
    }

    pub fn bool_not(mut self, dst: Val, src: Val) {
        self.instr(InstrData::BoolNot(instr::Unary { dst, src }));
        self.set_val_type(dst, self.cx.bool_type_ref());
    }

    pub fn local_to_eref(mut self, dst: Val, src: Val) {
        self.instr(InstrData::LocalToERef(instr::Unary { dst, src }));
        let typ = TypeRef::create(
            self.db,
            TypeKind::ERef(self.val_types[src].unwrap()),
            self.cx,
        );
        self.set_val_type(dst, typ);
    }

    pub fn init_struct(
        mut self,
        dst: Val,
        struct_type: TypeRef,
        field_values: impl IntoIterator<Item = Val>,
    ) {
        let fields = EntityList::from_iter(field_values, &mut self.func.val_lists);
        self.instr(InstrData::InitStruct(instr::InitStruct {
            dst,
            typ: struct_type,
            fields,
        }));
        self.set_val_type(dst, struct_type);
    }

    pub fn get_field(mut self, dst: Val, src: Val, field: Field) {
        self.instr(InstrData::GetField(instr::GetField {
            dst,
            src_struct: src,
            field,
        }));
        let TypeKind::Struct(strukt) = self.val_types[src]
            .unwrap()
            .resolve_in_builder(self.cx)
            .data(self.db)
        else {
            panic!("not a struct")
        };
        self.set_val_type(dst, strukt.fields[field].typ);
    }

    pub fn set_field(mut self, dst: Val, src_struct: Val, src_field_val: Val, field: Field) {
        self.instr(InstrData::SetField(instr::SetField {
            dst_struct: dst,
            src_struct,
            src_field_val,
            field,
        }));
        self.set_val_type(dst, self.val_types[src_struct].unwrap());
    }

    pub fn alloc(mut self, dst: Val, src: Val) {
        self.instr(InstrData::Alloc(instr::Alloc { dst_ref: dst, src }));
        let typ = TypeRef::create(
            self.db,
            TypeKind::MRef(self.val_types[src].unwrap()),
            self.cx,
        );
        self.set_val_type(dst, typ);
    }

    pub fn load(mut self, dst: Val, src_ref: Val) {
        self.instr(InstrData::Load(instr::Load { dst, src_ref }));

        let (TypeKind::MRef(t) | TypeKind::ERef(t)) = self.val_types[src_ref]
            .unwrap()
            .resolve_in_builder(self.cx)
            .data(self.db)
        else {
            panic!("not a reference")
        };
        self.set_val_type(dst, *t);
    }

    pub fn store(mut self, ref_: Val, val: Val) {
        self.instr(InstrData::Store(instr::Store { ref_, val }));
        // no set_val_type since no destination operands
    }

    pub fn make_field_eref(mut self, dst: Val, src: Val, field: Field) {
        self.instr(InstrData::MakeFieldERef(instr::MakeFieldERef {
            dst_ref: dst,
            src_ref: src,
            field,
        }));

        let TypeKind::Struct(strukt) = self.val_types[src]
            .unwrap()
            .resolve_in_builder(self.cx)
            .data(self.db)
        else {
            panic!("not a struct")
        };
        let typ = TypeRef::create(self.db, TypeKind::ERef(strukt.fields[field].typ), self.cx);
        self.set_val_type(dst, typ);
    }

    pub fn make_function_object(mut self, dst: Val, func: FuncRef, captures_ref: Val) {
        self.instr(InstrData::MakeFunctionObject(instr::MakeFunctionObject {
            dst,
            func,
            captures_ref,
        }));
        let typ = TypeRef::create(
            self.db,
            TypeKind::Func(FuncTypeData {
                param_types: func.resolve_header(self.db, self.cx).param_types.clone(),
                return_type: func.resolve_header(self.db, self.cx).return_type,
            }),
            self.cx,
        );
        self.set_val_type(dst, typ);
    }

    pub fn make_list(mut self, dst: Val, element_type: TypeRef) {
        self.instr(InstrData::MakeList(instr::MakeList { dst, element_type }));
        let typ = TypeRef::create(self.db, TypeKind::List(element_type), self.cx);
        self.set_val_type(dst, typ);
    }

    pub fn list_push(mut self, dst: Val, src_list: Val, src_element: Val) {
        self.instr(InstrData::ListPush(instr::ListPush {
            dst_list: Some(dst),
            src_list,
            src_element,
        }));
        self.set_val_type(dst, self.val_types[src_list].unwrap());
    }

    pub fn list_ref_push(mut self, src_list: Val, src_element: Val) {
        self.instr(InstrData::ListPush(instr::ListPush {
            dst_list: None,
            src_list,
            src_element,
        }));
        // no set_val_type since no destination operands
    }

    pub fn list_remove(mut self, dst: Val, src_list: Val, src_index: Val) {
        self.instr(InstrData::ListRemove(instr::ListRemove {
            dst_list: Some(dst),
            src_list,
            src_index,
        }));
        self.set_val_type(dst, self.val_types[src_list].unwrap());
    }

    pub fn list_ref_remove(mut self, src_list: Val, src_index: Val) {
        self.instr(InstrData::ListRemove(instr::ListRemove {
            dst_list: None,
            src_list,
            src_index,
        }));
        // no set_val_type since no destination operands
    }

    pub fn list_trunc(mut self, dst: Val, src_list: Val, new_len: Val) {
        self.instr(InstrData::ListTrunc(instr::ListTrunc {
            dst_list: Some(dst),
            src_list,
            new_len,
        }));
        self.set_val_type(dst, self.val_types[src_list].unwrap());
    }

    pub fn list_ref_trunc(mut self, src_list: Val, new_len: Val) {
        self.instr(InstrData::ListTrunc(instr::ListTrunc {
            dst_list: None,
            src_list,
            new_len,
        }));
        // no set_val_type since no destination operands
    }

    pub fn list_len(mut self, dst: Val, src: Val) {
        self.instr(InstrData::ListLen(instr::ListLen {
            dst_len: dst,
            src_list: src,
        }));
        self.set_val_type(dst, self.cx.int_type_ref());
    }

    pub fn list_get(mut self, dst: Val, src_list: Val, src_index: Val) {
        self.instr(InstrData::ListGet(instr::ListGet {
            dst_val: dst,
            src_list,
            src_index,
        }));
        self.set_val_type(
            dst,
            self.get_list_element_type(self.val_types[src_list].unwrap()),
        );
    }

    pub fn list_get_eref(mut self, dst: Val, src_list: Val, src_index: Val) {
        self.instr(InstrData::ListGetERef(instr::ListGetERef {
            dst_ref: dst,
            src_list,
            src_index,
        }));
        let typ = TypeRef::create(
            self.db,
            TypeKind::ERef(self.get_list_element_type(self.val_types[src_list].unwrap())),
            self.cx,
        );
        self.set_val_type(dst, typ);
    }

    fn get_list_element_type(&self, t: TypeRef) -> TypeRef {
        match t.resolve_in_builder(self.cx).data(self.db) {
            TypeKind::List(el) => *el,
            TypeKind::MRef(l) | TypeKind::ERef(l) => {
                match l.resolve_in_builder(self.cx).data(self.db) {
                    TypeKind::List(el) => *el,
                    _ => panic!("not a list"),
                }
            }
            _ => panic!("not a list"),
        }
    }

    fn set_val_type(&mut self, val: Val, typ: TypeRef) {
        if let Some(existing_type) = self.val_types[val] {
            assert_eq!(typ, existing_type, "value type mismatch");
        }
        self.val_types[val] = Some(typ);
    }

    fn instr(&mut self, instr: InstrData<'db>) {
        self.func.basic_blocks[self.block].instrs.push(instr);
    }
}
