use crate::{
    InstrData, TypeKind, ValId,
    ir::{
        AlgebraicTypeKind, BasicBlock, BasicBlockId, Constant, ContextBuilder, FieldId, FuncData,
        FuncHeader, FuncInstance, Type, TypeParam, TypeParamIndex, TypeParams, Val,
        instr::{self, CompareMode},
    },
};
use compact_str::CompactString;
use cranelift_entity::{EntityList, ListPool, PrimaryMap, SecondaryMap};
use salsa::Database;

/// Builder API for a `FuncData`.
pub struct FuncBuilder<'db> {
    db: &'db dyn Database,
    func: FuncData<'db>,
    current_block: BasicBlockId,
    /// Values created so far.
    /// Some value types may not yet be resolved.
    val_types: PrimaryMap<ValId, Option<Type<'db>>>,
    val_names: SecondaryMap<ValId, Option<CompactString>>,
}

impl<'db> FuncBuilder<'db> {
    pub fn new(
        db: &'db dyn Database,
        name: impl Into<CompactString>,
        captures_type: Type<'db>,
        return_type: Type<'db>,
        _cx: &mut ContextBuilder<'db>,
    ) -> Self {
        let mut basic_blocks = PrimaryMap::new();
        let entry_block = basic_blocks.push(BasicBlock::default());
        let mut val_lists = ListPool::new();
        let mut val_types = PrimaryMap::new();

        let captures_val = val_types.push(Some(Type::new(db, TypeKind::MRef(captures_type))));
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
                    type_params: TypeParams::new(),
                },

                vals: PrimaryMap::default(),

                basic_blocks,
                entry_block,
                val_lists,
            },
            current_block: entry_block,
            val_types,
            val_names: SecondaryMap::new(),
        }
    }

    pub fn append_type_param(&mut self, type_param: TypeParam<'db>) -> TypeParamIndex {
        self.func.header.type_params.push(type_param)
    }

    pub fn append_param(&mut self, typ: Type<'db>) -> ValId {
        let val = self.val();
        self.val_types[val] = Some(typ);
        self.func.header.param_types.push(typ);
        self.func.basic_blocks[self.func.entry_block]
            .params
            .push(val, &mut self.func.val_lists);
        val
    }

    pub fn append_named_param(&mut self, typ: Type<'db>, name: impl Into<CompactString>) -> ValId {
        let param = self.append_param(typ);
        self.val_names[param] = Some(name.into());
        param
    }

    pub fn append_block_param(&mut self, typ: Type<'db>) -> ValId {
        let val = self.val();
        self.val_types[val] = Some(typ);
        self.func.basic_blocks[self.current_block]
            .params
            .push(val, &mut self.func.val_lists);
        val
    }

    pub fn append_named_block_param(
        &mut self,
        typ: Type<'db>,
        name: impl Into<CompactString>,
    ) -> ValId {
        let val = self.append_block_param(typ);
        self.val_names[val] = Some(name.into());
        val
    }

    pub fn set_val_name(&mut self, val: ValId, name: impl Into<CompactString>) {
        self.val_names[val] = Some(name.into());
    }

    pub fn create_block(&mut self) -> BasicBlockId {
        self.func.basic_blocks.push(BasicBlock::default())
    }

    pub fn set_block_name(&mut self, bb: BasicBlockId, name: impl Into<CompactString>) {
        self.func.basic_blocks[bb].name = Some(name.into());
    }

    pub fn entry_block(&self) -> BasicBlockId {
        self.func.entry_block
    }

    pub fn block_param(&self, i: usize) -> ValId {
        self.func.basic_blocks[self.current_block]
            .params
            .get(i, &self.func.val_lists)
            .unwrap()
    }

    pub fn switch_to_block(&mut self, block: BasicBlockId) {
        self.current_block = block;
    }

    /// Creates a new value. Its type is not yet
    /// known; it is set when the value is first used
    /// as a destination operand.
    pub fn val(&mut self) -> ValId {
        self.val_types.push(None)
    }

    pub fn named_val(&mut self, name: impl Into<CompactString>) -> ValId {
        let val = self.val();
        self.val_names[val] = Some(name.into());
        val
    }

    pub fn val_type(&self, val: ValId) -> Type<'db> {
        self.val_types[val].expect("value type not bound")
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

    pub fn build(mut self, _cx: &mut ContextBuilder<'db>) -> FuncData<'db> {
        // Resolve final value types
        for (val, val_type) in self.val_types {
            // If value type was never resolved
            // then the value is unused - any type is
            // valid - use unit type
            let val_type = val_type.unwrap_or_else(|| Type::unit(self.db));
            // Same ID should be allocated since
            // same order of insertion into PrimaryMap
            assert_eq!(
                val,
                self.func.vals.push(Val {
                    typ: val_type,
                    name: self.val_names[val].take()
                })
            );
        }

        self.func
    }
}

pub struct FuncInstrBuilder<'a, 'db> {
    #[allow(unused)]
    db: &'db dyn Database,
    cx: &'a mut ContextBuilder<'db>,
    func: &'a mut FuncData<'db>,
    block: BasicBlockId,
    val_types: &'a mut PrimaryMap<ValId, Option<Type<'db>>>,
}

impl<'a, 'db> FuncInstrBuilder<'a, 'db> {
    pub fn jump(self, target: BasicBlockId) {
        self.jump_with_args(target, [])
    }

    pub fn jump_with_args(mut self, target: BasicBlockId, args: impl IntoIterator<Item = ValId>) {
        let args = EntityList::from_iter(args, &mut self.func.val_lists);
        self.instr(InstrData::Jump(instr::Jump { target, args }));
    }

    pub fn branch(self, condition: ValId, target_true: BasicBlockId, target_false: BasicBlockId) {
        self.branch_with_args(condition, target_true, [], target_false, [])
    }

    pub fn branch_with_args(
        mut self,
        condition: ValId,
        target_true: BasicBlockId,
        args_true: impl IntoIterator<Item = ValId>,
        target_false: BasicBlockId,
        args_false: impl IntoIterator<Item = ValId>,
    ) {
        let args_true = EntityList::from_iter(args_true, &mut self.func.val_lists);
        let args_false = EntityList::from_iter(args_false, &mut self.func.val_lists);
        self.instr(InstrData::Branch(instr::Branch {
            target_true,
            target_false,
            args_true,
            args_false,
            condition,
        }));
    }

    pub fn call(
        mut self,
        return_value_dst: ValId,
        func: FuncInstance<'db>,
        args: impl IntoIterator<Item = ValId>,
    ) {
        let args = EntityList::from_iter(args, &mut self.func.val_lists);
        self.instr(InstrData::Call(instr::Call {
            func,
            args,
            return_value_dst,
        }));
        self.set_val_type(return_value_dst, func.return_type(self.db, &self.cx));
    }

    pub fn return_(mut self, return_value: ValId) {
        self.instr(InstrData::Return(instr::Return { return_value }));
    }

    pub fn copy(mut self, dst: ValId, src: ValId) {
        self.instr(InstrData::Copy(instr::Unary { dst, src }));
        self.set_val_type(dst, self.val_types[src].unwrap());
    }

    pub fn constant(mut self, dst: ValId, constant: Constant<'db>) {
        self.instr(InstrData::Constant(instr::ConstantInstr { dst, constant }));
        let typ = constant.value(self.db).typ();
        self.set_val_type(dst, Type::new(self.db, typ))
    }

    pub fn int_add(mut self, dst: ValId, src1: ValId, src2: ValId) {
        self.instr(InstrData::IntAdd(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, Type::int(self.db));
    }

    pub fn int_sub(mut self, dst: ValId, src1: ValId, src2: ValId) {
        self.instr(InstrData::IntSub(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, Type::int(self.db));
    }

    pub fn int_mul(mut self, dst: ValId, src1: ValId, src2: ValId) {
        self.instr(InstrData::IntMul(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, Type::int(self.db));
    }

    pub fn int_div(mut self, dst: ValId, src1: ValId, src2: ValId) {
        self.instr(InstrData::IntDiv(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, Type::int(self.db));
    }

    pub fn int_cmp(mut self, dst: ValId, src1: ValId, src2: ValId, mode: CompareMode) {
        self.instr(InstrData::IntCmp(instr::Cmp {
            dst,
            src1,
            src2,
            mode,
        }));
        self.set_val_type(dst, Type::bool(self.db));
    }

    pub fn real_add(mut self, dst: ValId, src1: ValId, src2: ValId) {
        self.instr(InstrData::RealAdd(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, Type::real(self.db));
    }

    pub fn real_sub(mut self, dst: ValId, src1: ValId, src2: ValId) {
        self.instr(InstrData::RealSub(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, Type::real(self.db));
    }

    pub fn real_mul(mut self, dst: ValId, src1: ValId, src2: ValId) {
        self.instr(InstrData::RealMul(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, Type::real(self.db));
    }

    pub fn real_div(mut self, dst: ValId, src1: ValId, src2: ValId) {
        self.instr(InstrData::RealDiv(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, Type::real(self.db));
    }

    pub fn real_cmp(mut self, dst: ValId, src1: ValId, src2: ValId, mode: CompareMode) {
        self.instr(InstrData::RealCmp(instr::Cmp {
            dst,
            src1,
            src2,
            mode,
        }));
        self.set_val_type(dst, Type::bool(self.db));
    }

    pub fn real_to_int(mut self, dst: ValId, src: ValId) {
        self.instr(InstrData::RealToInt(instr::Unary { dst, src }));
        self.set_val_type(dst, Type::int(self.db));
    }

    pub fn int_to_real(mut self, dst: ValId, src: ValId) {
        self.instr(InstrData::IntToReal(instr::Unary { dst, src }));
        self.set_val_type(dst, Type::real(self.db));
    }

    pub fn byte_to_int(mut self, dst: ValId, src: ValId) {
        self.instr(InstrData::ByteToInt(instr::Unary { dst, src }));
        self.set_val_type(dst, Type::int(self.db));
    }

    pub fn int_to_byte(mut self, dst: ValId, src: ValId) {
        self.instr(InstrData::IntToByte(instr::Unary { dst, src }));
        self.set_val_type(dst, Type::bool(self.db));
    }

    pub fn bool_and(mut self, dst: ValId, src1: ValId, src2: ValId) {
        self.instr(InstrData::BoolAnd(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, Type::bool(self.db));
    }

    pub fn bool_or(mut self, dst: ValId, src1: ValId, src2: ValId) {
        self.instr(InstrData::BoolOr(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, Type::bool(self.db));
    }

    pub fn bool_xor(mut self, dst: ValId, src1: ValId, src2: ValId) {
        self.instr(InstrData::BoolXor(instr::Binary { dst, src1, src2 }));
        self.set_val_type(dst, Type::bool(self.db));
    }

    pub fn bool_not(mut self, dst: ValId, src: ValId) {
        self.instr(InstrData::BoolNot(instr::Unary { dst, src }));
        self.set_val_type(dst, Type::bool(self.db));
    }

    pub fn init_struct(
        mut self,
        dst: ValId,
        struct_type: Type<'db>,
        field_values: impl IntoIterator<Item = ValId>,
    ) {
        let fields = EntityList::from_iter(field_values, &mut self.func.val_lists);
        self.instr(InstrData::InitStruct(instr::InitStruct {
            dst,
            typ: struct_type,
            fields,
        }));
        self.set_val_type(dst, struct_type);
    }

    pub fn get_field(mut self, dst: ValId, src: ValId, field: FieldId) {
        self.instr(InstrData::GetField(instr::GetField {
            dst,
            src_struct: src,
            field,
        }));
        let TypeKind::Algebraic(adt_instance) = self.val_types[src].unwrap().kind(self.db) else {
            panic!("not an ADT")
        };

        let AlgebraicTypeKind::Struct(strukt_data) = adt_instance.adt.kind(self.db, &self.cx);

        let typ = strukt_data.fields[field]
            .typ
            .substitute_type_args(self.db, &adt_instance.type_args);
        self.set_val_type(dst, typ);
    }

    pub fn set_field(
        mut self,
        dst: ValId,
        src_struct: ValId,
        src_field_val: ValId,
        field: FieldId,
    ) {
        self.instr(InstrData::SetField(instr::SetField {
            dst_struct: dst,
            src_struct,
            src_field_val,
            field,
        }));
        self.set_val_type(dst, self.val_types[src_struct].unwrap());
    }

    pub fn alloc(mut self, dst: ValId, src: ValId) {
        self.instr(InstrData::Alloc(instr::Alloc { dst_ref: dst, src }));
        let typ = TypeKind::MRef(self.val_types[src].unwrap());
        self.set_val_type(dst, Type::new(self.db, typ));
    }

    pub fn load(mut self, dst: ValId, src_ref: ValId) {
        self.instr(InstrData::Load(instr::Load { dst, src_ref }));

        let TypeKind::MRef(t) = self.val_types[src_ref].unwrap().kind(self.db) else {
            panic!("not a reference")
        };
        self.set_val_type(dst, *t);
    }

    pub fn store(mut self, ref_: ValId, val: ValId) {
        self.instr(InstrData::Store(instr::Store { ref_, val }));
        // no set_val_type since no destination operands
    }

    pub fn make_field_mref(mut self, dst: ValId, src: ValId, field: FieldId) {
        self.instr(InstrData::MakeFieldMRef(instr::MakeFieldMRef {
            dst_ref: dst,
            src_ref: src,
            field,
        }));

        let TypeKind::MRef(pointee) = self.val_types[src].unwrap().kind(self.db) else {
            panic!("not a reference")
        };
        let TypeKind::Algebraic(adt_instance) = pointee.kind(self.db) else {
            panic!("not an ADT")
        };

        let AlgebraicTypeKind::Struct(strukt_data) = adt_instance.adt.kind(self.db, &self.cx);

        let typ = strukt_data.fields[field]
            .typ
            .substitute_type_args(self.db, &adt_instance.type_args);
        self.set_val_type(dst, typ);
    }

    pub fn make_list(mut self, dst: ValId, element_type: Type<'db>) {
        self.instr(InstrData::MakeList(instr::MakeList { dst, element_type }));
        let typ = Type::new(self.db, TypeKind::List(element_type));
        self.set_val_type(dst, typ);
    }

    pub fn list_push(mut self, dst: ValId, src_list: ValId, src_element: ValId) {
        self.instr(InstrData::ListPush(instr::ListPush {
            dst_list: Some(dst),
            src_list,
            src_element,
        }));
        self.set_val_type(dst, self.val_types[src_list].unwrap());
    }

    pub fn list_ref_push(mut self, src_list: ValId, src_element: ValId) {
        self.instr(InstrData::ListPush(instr::ListPush {
            dst_list: None,
            src_list,
            src_element,
        }));
        // no set_val_type since no destination operands
    }

    pub fn list_remove(mut self, dst: ValId, src_list: ValId, src_index: ValId) {
        self.instr(InstrData::ListRemove(instr::ListRemove {
            dst_list: Some(dst),
            src_list,
            src_index,
        }));
        self.set_val_type(dst, self.val_types[src_list].unwrap());
    }

    pub fn list_ref_remove(mut self, src_list: ValId, src_index: ValId) {
        self.instr(InstrData::ListRemove(instr::ListRemove {
            dst_list: None,
            src_list,
            src_index,
        }));
        // no set_val_type since no destination operands
    }

    pub fn list_trunc(mut self, dst: ValId, src_list: ValId, new_len: ValId) {
        self.instr(InstrData::ListTrunc(instr::ListTrunc {
            dst_list: Some(dst),
            src_list,
            new_len,
        }));
        self.set_val_type(dst, self.val_types[src_list].unwrap());
    }

    pub fn list_ref_trunc(mut self, src_list: ValId, new_len: ValId) {
        self.instr(InstrData::ListTrunc(instr::ListTrunc {
            dst_list: None,
            src_list,
            new_len,
        }));
        // no set_val_type since no destination operands
    }

    pub fn list_len(mut self, dst: ValId, src: ValId) {
        self.instr(InstrData::ListLen(instr::ListLen {
            dst_len: dst,
            src_list: src,
        }));
        self.set_val_type(dst, Type::int(self.db));
    }

    pub fn list_get(mut self, dst: ValId, src_list: ValId, src_index: ValId) {
        self.instr(InstrData::ListGet(instr::ListGet {
            dst_val: dst,
            src_list,
            src_index,
        }));
        self.set_val_type(
            dst,
            self.get_list_element_type(self.val_types[src_list].unwrap().kind(self.db)),
        );
    }

    pub fn list_get_mref(mut self, dst: ValId, src_list: ValId, src_index: ValId) {
        self.instr(InstrData::ListGetMRef(instr::ListGetMRef {
            dst_ref: dst,
            src_list,
            src_index,
        }));
        let typ = TypeKind::MRef(
            self.get_list_element_type(self.val_types[src_list].unwrap().kind(self.db)),
        );
        self.set_val_type(dst, Type::new(self.db, typ));
    }

    fn get_list_element_type(&self, t: &TypeKind<'db>) -> Type<'db> {
        match t {
            TypeKind::List(el) => *el,
            TypeKind::MRef(l) => match l.kind(self.db) {
                TypeKind::List(el) => *el,
                _ => panic!("not a list"),
            },
            _ => panic!("not a list"),
        }
    }

    fn set_val_type(&mut self, val: ValId, typ: Type<'db>) {
        if let Some(existing_type) = self.val_types[val].as_ref() {
            assert_eq!(&typ, existing_type, "value type mismatch");
        }
        self.val_types[val] = Some(typ);
    }

    fn instr(&mut self, instr: InstrData<'db>) {
        self.func.basic_blocks[self.block].instrs.push(instr);
    }
}
