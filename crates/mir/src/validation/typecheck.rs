use crate::{
    module::{BasicBlock, Context, FuncData, FuncTypeData, StructTypeData, TypeRef},
    validation::ValidationError,
    InstrData, PrimType, TypeKind, Val,
};
use cranelift_entity::EntityList;
use fir_core::Db;

/// Verifies that operands have the correct type for each instruction.
pub fn verify_instr_types<'db>(
    db: &'db Db,
    cx: Context<'db>,
    func: &FuncData,
) -> Result<(), ValidationError> {
    let verifier = InstrTypeVerifier { func, db, cx };
    verifier.verify_entry_block_params()?;
    for (_, block) in &func.basic_blocks {
        for instr in &block.instrs {
            verifier.verify_types_for_instr(*instr)?;
        }
    }

    Ok(())
}

struct InstrTypeVerifier<'a, 'db> {
    cx: Context<'db>,
    func: &'a FuncData<'db>,
    db: &'db Db,
}

impl<'a, 'db> InstrTypeVerifier<'a, 'db> {
    fn verify_types_for_instr(&self, instr: InstrData) -> Result<(), ValidationError> {
        match instr {
            InstrData::Jump(ins) => {
                self.verify_basic_block_args(ins.target, &ins.args)?;
            }
            InstrData::Branch(ins) => {
                self.verify_type_data_matches(ins.condition, &[TypeKind::Prim(PrimType::Bool)])?;
                self.verify_basic_block_args(ins.target_true, &ins.args_true)?;
                self.verify_basic_block_args(ins.target_false, &ins.args_false)?;
            }
            InstrData::Call(ins) => {
                if ins
                    .func
                    .data(self.db, self.cx)
                    .header
                    .captures_type
                    .data(self.db, self.cx)
                    != &TypeKind::Prim(PrimType::Unit)
                {
                    return Err(ValidationError::new(
                        "can't make a direct call to a function with non-unit captures type",
                    ));
                }

                self.verify_function_args(
                    &ins.func.data(self.db, self.cx).header.param_types,
                    &ins.args,
                )?;
                self.verify_type_equals(
                    ins.return_value_dst,
                    ins.func.data(self.db, self.cx).header.return_type,
                )?;
            }
            InstrData::CallIndirect(ins) => {
                let TypeKind::Func(func_typ) = self.type_data_of(ins.func) else {
                    return Err(ValidationError::new(
                        "CallIndirect requires a function object",
                    ));
                };
                self.verify_function_args(&func_typ.param_types, &ins.args)?;
                self.verify_type_equals(ins.return_value_dst, func_typ.return_type)?;
            }
            InstrData::Return(ins) => {
                self.verify_type_equals(ins.return_value, self.func.header.return_type)?;
            }
            InstrData::Copy(ins) => {
                self.verify_type_equals(ins.dst, self.type_of(ins.src))?;
            }
            InstrData::Constant(ins) => {
                self.verify_type_data_matches(ins.dst, &[ins.constant.data(self.db).typ()])?;
            }
            InstrData::IntAdd(ins)
            | InstrData::IntSub(ins)
            | InstrData::IntMul(ins)
            | InstrData::IntDiv(ins) => {
                self.verify_type_data_matches(ins.src1, &[TypeKind::Prim(PrimType::Int)])?;
                self.verify_type_data_matches(ins.src2, &[TypeKind::Prim(PrimType::Int)])?;
                self.verify_type_data_matches(ins.dst, &[TypeKind::Prim(PrimType::Int)])?;
            }
            InstrData::IntCmp(ins) => {
                self.verify_type_data_matches(ins.src1, &[TypeKind::Prim(PrimType::Int)])?;
                self.verify_type_data_matches(ins.src2, &[TypeKind::Prim(PrimType::Int)])?;
                self.verify_type_data_matches(ins.dst, &[TypeKind::Prim(PrimType::Bool)])?;
            }
            InstrData::RealAdd(ins)
            | InstrData::RealSub(ins)
            | InstrData::RealMul(ins)
            | InstrData::RealDiv(ins) => {
                self.verify_type_data_matches(ins.src1, &[TypeKind::Prim(PrimType::Real)])?;
                self.verify_type_data_matches(ins.src2, &[TypeKind::Prim(PrimType::Real)])?;
                self.verify_type_data_matches(ins.dst, &[TypeKind::Prim(PrimType::Real)])?;
            }
            InstrData::RealCmp(ins) => {
                self.verify_type_data_matches(ins.src1, &[TypeKind::Prim(PrimType::Real)])?;
                self.verify_type_data_matches(ins.src2, &[TypeKind::Prim(PrimType::Real)])?;
                self.verify_type_data_matches(ins.dst, &[TypeKind::Prim(PrimType::Bool)])?;
            }
            InstrData::RealToInt(ins) => {
                self.verify_type_data_matches(ins.src, &[TypeKind::Prim(PrimType::Real)])?;
                self.verify_type_data_matches(ins.dst, &[TypeKind::Prim(PrimType::Int)])?;
            }
            InstrData::IntToReal(ins) => {
                self.verify_type_data_matches(ins.src, &[TypeKind::Prim(PrimType::Int)])?;
                self.verify_type_data_matches(ins.dst, &[TypeKind::Prim(PrimType::Real)])?;
            }
            InstrData::ByteToInt(ins) => {
                self.verify_type_data_matches(ins.src, &[TypeKind::Prim(PrimType::Byte)])?;
                self.verify_type_data_matches(ins.dst, &[TypeKind::Prim(PrimType::Int)])?;
            }
            InstrData::IntToByte(ins) => {
                self.verify_type_data_matches(ins.src, &[TypeKind::Prim(PrimType::Int)])?;
                self.verify_type_data_matches(ins.dst, &[TypeKind::Prim(PrimType::Byte)])?;
            }
            InstrData::BoolAnd(ins) | InstrData::BoolOr(ins) | InstrData::BoolXor(ins) => {
                self.verify_type_data_matches(ins.src1, &[TypeKind::Prim(PrimType::Bool)])?;
                self.verify_type_data_matches(ins.src2, &[TypeKind::Prim(PrimType::Bool)])?;
                self.verify_type_data_matches(ins.dst, &[TypeKind::Prim(PrimType::Bool)])?;
            }
            InstrData::BoolNot(ins) => {
                self.verify_type_data_matches(ins.src, &[TypeKind::Prim(PrimType::Bool)])?;
                self.verify_type_data_matches(ins.dst, &[TypeKind::Prim(PrimType::Bool)])?;
            }
            InstrData::LocalToERef(ins) => {
                let pointee_type = self.type_of(ins.src);
                self.verify_type_data_matches(ins.dst, &[TypeKind::ERef(pointee_type)])?;
            }
            InstrData::InitStruct(ins) => {
                let TypeKind::Struct(struct_data) = self.type_data_of(ins.dst) else {
                    return Err(ValidationError::new("expected struct type"));
                };
                let field_vals = ins.fields.as_slice(&self.func.val_lists);
                if field_vals.len() != struct_data.fields.len() {
                    return Err(ValidationError::new(
                        "wrong number of fields for struct init",
                    ));
                }

                for (field_val, field) in
                    field_vals.iter().copied().zip(struct_data.fields.values())
                {
                    self.verify_type_equals(field_val, field.typ)?;
                }
            }
            InstrData::GetField(ins) => {
                let struct_data = self.expect_struct(ins.dst)?;
                let field = &struct_data.fields[ins.field];
                self.verify_type_equals(ins.dst, field.typ)?;
            }
            InstrData::SetField(ins) => {
                let struct_data = self.expect_struct(ins.src_struct)?;
                let field = &struct_data.fields[ins.field];
                self.verify_type_equals(ins.src_field_val, field.typ)?;
                self.verify_type_equals(ins.dst_struct, self.type_of(ins.src_struct))?;
            }
            InstrData::Alloc(ins) => {
                self.verify_type_data_matches(
                    ins.dst_ref,
                    &[TypeKind::MRef(self.type_of(ins.src))],
                )?;
            }
            InstrData::Load(ins) => {
                let pointee = self.expect_any_ref(ins.src_ref)?;
                self.verify_type_equals(ins.dst, pointee)?;
            }
            InstrData::Store(ins) => {
                self.verify_type_data_matches(
                    ins.ref_,
                    &[
                        TypeKind::MRef(self.type_of(ins.val)),
                        TypeKind::ERef(self.type_of(ins.val)),
                    ],
                )?;
            }
            InstrData::MakeFieldERef(ins) => {
                let pointee = self.expect_any_ref(ins.src_ref)?;
                let struct_data = match pointee.data(self.db, self.cx) {
                    TypeKind::Struct(s) => s,
                    _ => return Err(ValidationError::new("expected reference to struct")),
                };
                let field = &struct_data.fields[ins.field];
                self.verify_type_data_matches(ins.dst_ref, &[TypeKind::ERef(field.typ)])?;
            }
            InstrData::MakeFunctionObject(ins) => {
                let func_object_data = ins.func.data(self.db, self.cx);
                self.verify_type_data_matches(
                    ins.dst,
                    &[TypeKind::Func(FuncTypeData {
                        param_types: func_object_data.header.param_types.clone(),
                        return_type: func_object_data.header.return_type,
                    })],
                )?;
                self.verify_type_data_matches(
                    ins.captures_ref,
                    &[TypeKind::MRef(func_object_data.header.captures_type)],
                )?;
            }
            InstrData::MakeList(ins) => {
                self.verify_type_data_matches(ins.dst, &[TypeKind::List(ins.element_type)])?;
            }
            InstrData::ListPush(ins) => {
                let element_type = self.expect_list_or_list_ref(ins.src_list)?;
                self.verify_type_equals(ins.src_element, element_type)?;
                if self.is_ref(self.type_of(ins.src_list)) {
                    if ins.dst_list.is_some() {
                        return Err(ValidationError::new("for list modifying instructions operating on a reference, dst_list must be None"));
                    }
                } else {
                    let dst_list = ins.dst_list.ok_or_else(|| ValidationError::new("for list modifying instructions operating on values, dst_list must be Some"))?;
                    self.verify_type_data_matches(dst_list, &[TypeKind::List(element_type)])?;
                }
            }
            InstrData::ListRemove(ins) => {
                self.verify_type_data_matches(ins.src_index, &[TypeKind::Prim(PrimType::Int)])?;

                let element_type = self.expect_list_or_list_ref(ins.src_list)?;
                if self.is_ref(self.type_of(ins.src_list)) {
                    if ins.dst_list.is_some() {
                        return Err(ValidationError::new("for list modifying instructions operating on a reference, dst_list must be None"));
                    }
                } else {
                    let dst_list = ins.dst_list.ok_or_else(|| ValidationError::new("for list modifying instructions operating on values, dst_list must be Some"))?;
                    self.verify_type_data_matches(dst_list, &[TypeKind::List(element_type)])?;
                }
            }
            InstrData::ListTrunc(ins) => {
                self.verify_type_data_matches(ins.new_len, &[TypeKind::Prim(PrimType::Int)])?;

                let element_type = self.expect_list_or_list_ref(ins.src_list)?;
                if self.is_ref(self.type_of(ins.src_list)) {
                    if ins.dst_list.is_some() {
                        return Err(ValidationError::new("for list modifying instructions operating on a reference, dst_list must be None"));
                    }
                } else {
                    let dst_list = ins.dst_list.ok_or_else(|| ValidationError::new("for list modifying instructions operating on values, dst_list must be Some"))?;
                    self.verify_type_data_matches(dst_list, &[TypeKind::List(element_type)])?;
                }
            }
            InstrData::ListLen(ins) => {
                self.expect_list_or_list_ref(ins.src_list)?;
                self.verify_type_data_matches(ins.dst_len, &[TypeKind::Prim(PrimType::Int)])?;
            }
            InstrData::ListGet(ins) => {
                let element_type = self.expect_list_or_list_ref(ins.src_list)?;
                self.verify_type_data_matches(ins.src_index, &[TypeKind::Prim(PrimType::Int)])?;
                self.verify_type_equals(ins.dst_val, element_type)?;
            }
            InstrData::ListGetERef(ins) => {
                let element_type = self.expect_list_or_list_ref(ins.src_list)?;
                self.verify_type_data_matches(ins.src_index, &[TypeKind::Prim(PrimType::Int)])?;
                self.verify_type_data_matches(ins.dst_ref, &[TypeKind::ERef(element_type)])?;
            }
        }
        Ok(())
    }

    fn verify_entry_block_params(&self) -> Result<(), ValidationError> {
        let mut expected_param_types = vec![TypeKind::MRef(self.func.header.captures_type)];
        expected_param_types.extend(
            self.func
                .header
                .param_types
                .iter()
                .map(|&t| t.data(self.db, self.cx).clone()),
        );

        let entry_block = &self.func.basic_blocks[self.func.entry_block];
        let entry_block_params = entry_block.params.as_slice(&self.func.val_lists);

        if expected_param_types.len() != entry_block_params.len() {
            return Err(ValidationError::new(
                "wrong number of parameters for entry block",
            ));
        }

        for (expected_type, val) in expected_param_types
            .into_iter()
            .zip(entry_block_params.iter().copied())
        {
            if self.type_data_of(val) != &expected_type {
                return Err(ValidationError::new(format!(
                    "wrong parameter type for entry block: expected {expected_type:?}, found {:?}",
                    self.type_data_of(val)
                )));
            }
        }

        Ok(())
    }

    fn type_of(&self, val: Val) -> TypeRef {
        self.func.vals[val].typ
    }

    fn type_data_of(&self, val: Val) -> &'db TypeKind {
        self.func.vals[val].typ.data(self.db, self.cx)
    }

    fn verify_type_data_matches(
        &self,
        val: Val,
        allowed_types: &[TypeKind],
    ) -> Result<(), ValidationError> {
        let typ = self.func.vals[val].typ;
        if !allowed_types.contains(typ.data(self.db, self.cx)) {
            return Err(ValidationError::new(format!(
                "expected one of {allowed_types:?}, found {:?}",
                typ.data(self.db, self.cx)
            )));
        }
        Ok(())
    }

    fn verify_type_equals(&self, val: Val, typ: TypeRef) -> Result<(), ValidationError> {
        let actual_typ = self.func.vals[val].typ;
        if typ != actual_typ {
            return Err(ValidationError::new(format!(
                "wrong type: expected {:?}, found {:?}",
                typ.data(self.db, self.cx),
                actual_typ.data(self.db, self.cx)
            )));
        }
        Ok(())
    }

    fn verify_basic_block_args(
        &self,
        block: BasicBlock,
        args: &EntityList<Val>,
    ) -> Result<(), ValidationError> {
        let params = self.func.basic_blocks[block]
            .params
            .as_slice(&self.func.val_lists);
        let args = args.as_slice(&self.func.val_lists);

        if params.len() != args.len() {
            return Err(ValidationError::new(
                "wrong number of arguments to basic block",
            ));
        }

        for (param, arg) in params.iter().copied().zip(args.iter().copied()) {
            if self.func.vals[param].typ != self.func.vals[arg].typ {
                return Err(ValidationError::new(
                    "wrong type as argument to basic block",
                ));
            }
        }

        Ok(())
    }

    fn verify_function_args(
        &self,
        param_types: &[TypeRef],
        args: &EntityList<Val>,
    ) -> Result<(), ValidationError> {
        let args = args.as_slice(&self.func.val_lists);

        if param_types.len() != args.len() {
            return Err(ValidationError::new(
                "wrong number of arguments to function",
            ));
        }

        for (param, arg) in param_types.iter().copied().zip(args.iter().copied()) {
            if param != self.func.vals[arg].typ {
                return Err(ValidationError::new("wrong type as argument to function"));
            }
        }

        Ok(())
    }

    fn expect_struct(&self, val: Val) -> Result<&'db StructTypeData, ValidationError> {
        match self.type_data_of(val) {
            TypeKind::Struct(s) => Ok(s),
            _ => Err(ValidationError::new("expected struct type")),
        }
    }

    fn expect_any_ref(&self, val: Val) -> Result<TypeRef, ValidationError> {
        match self.type_data_of(val) {
            TypeKind::MRef(t) => Ok(*t),
            TypeKind::ERef(t) => Ok(*t),
            _ => Err(ValidationError::new("expected mref or eref")),
        }
    }

    fn expect_list_or_list_ref(&self, val: Val) -> Result<TypeRef, ValidationError> {
        match self.type_data_of(val) {
            TypeKind::List(t) => Ok(*t),
            TypeKind::ERef(l) | TypeKind::MRef(l)
                if let TypeKind::List(t) = l.data(self.db, self.cx) =>
            {
                Ok(*t)
            }
            _ => Err(ValidationError::new("expected list or reference to list")),
        }
    }

    fn is_ref(&self, t: TypeRef) -> bool {
        matches!(
            t.data(self.db, self.cx),
            TypeKind::MRef(_) | TypeKind::ERef(_)
        )
    }
}
