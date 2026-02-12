use crate::{
    InstrData, PrimType, TypeKind, ValId,
    ir::{
        AbstractFuncInstance, AlgebraicTypeKind, BasicBlockId, Context, FuncData, MaybeAssocFunc,
        StructTypeData, TraitImpl, Type, TypeArgs, TypeParamId,
    },
    trait_resolution,
    validation::ValidationError,
};
use cranelift_entity::EntityList;
use salsa::Database;

pub fn verify_all<'db>(db: &'db dyn Database, cx: Context<'db>) -> Result<(), ValidationError> {
    for func in cx.data(db).funcs.values() {
        verify_instr_types(db, cx, func.data(db))?;
    }

    for trait_impl in cx.data(db).trait_impls.values() {
        verify_trait_impl(db, cx, *trait_impl)?;
    }

    Ok(())
}

/// Verifies that operands have the correct type for each instruction.
pub fn verify_instr_types<'db>(
    db: &'db dyn Database,
    cx: Context<'db>,
    func: &FuncData,
) -> Result<(), ValidationError> {
    let verifier = InstrTypeVerifier { func, db, cx };
    verifier.verify_entry_block_params()?;
    for (_, block) in &func.basic_blocks {
        for (_, instr) in &block.instrs {
            verifier.verify_types_for_instr(instr)?;
        }
    }

    Ok(())
}

struct InstrTypeVerifier<'a, 'db> {
    cx: Context<'db>,
    func: &'a FuncData<'db>,
    db: &'db dyn Database,
}

impl<'a, 'db> InstrTypeVerifier<'a, 'db> {
    fn verify_types_for_instr(&self, instr: &InstrData) -> Result<(), ValidationError> {
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
                self.verify_func_instance(ins.func)?;

                self.verify_function_args(&ins.func.param_types(self.db, &self.cx), &ins.args)?;
                self.verify_type_equals(
                    ins.return_value_dst,
                    ins.func.return_type(self.db, &self.cx),
                )?;
            }
            InstrData::Return(ins) => {
                self.verify_type_equals(ins.return_value, self.func.header.return_type)?;
            }
            InstrData::Copy(ins) => {
                self.verify_type_equals(ins.dst, self.type_of(ins.src))?;
            }
            InstrData::Constant(ins) => {
                self.verify_type_data_matches(ins.dst, &[ins.constant.value(self.db).typ()])?;
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
            InstrData::InitStruct(ins) => {
                let (struct_data, type_args) = self.expect_struct(ins.dst)?;
                let field_vals = ins.fields.as_slice(&self.func.val_lists);
                if field_vals.len() != struct_data.fields.len() {
                    return Err(ValidationError::new(
                        "wrong number of fields for struct init",
                    ));
                }

                for (field_val, field) in
                    field_vals.iter().copied().zip(struct_data.fields.values())
                {
                    self.verify_type_equals(
                        field_val,
                        field.typ.substitute_type_args(self.db, type_args),
                    )?;
                }
            }
            InstrData::GetField(ins) => {
                let (struct_data, type_args) = self.expect_struct(ins.src_struct)?;
                let field = &struct_data.fields[ins.field];
                self.verify_type_equals(
                    ins.dst,
                    field.typ.substitute_type_args(self.db, type_args),
                )?;
            }
            InstrData::SetField(ins) => {
                let (struct_data, type_args) = self.expect_struct(ins.src_struct)?;
                let field = &struct_data.fields[ins.field];
                self.verify_type_equals(
                    ins.src_field_val,
                    field.typ.substitute_type_args(self.db, type_args),
                )?;
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
                self.verify_type_data_matches(ins.ref_, &[TypeKind::MRef(self.type_of(ins.val))])?;
            }
            InstrData::MakeFieldMRef(ins) => {
                let pointee = self.expect_any_ref(ins.src_ref)?;
                let (struct_data, type_args) = self.expect_struct_kind(pointee)?;
                let field = &struct_data.fields[ins.field];
                self.verify_type_data_matches(
                    ins.dst_ref,
                    &[TypeKind::MRef(
                        field.typ.substitute_type_args(self.db, type_args),
                    )],
                )?;
            }
            InstrData::MakeBufref(ins) => {
                self.verify_type_data_matches(ins.dst, &[TypeKind::Bufref(ins.element_type)])?;
            }
            InstrData::BufrefPush(ins) => {
                let element_type = self.expect_bufref(ins.src_bufref)?;
                self.verify_type_equals(ins.src_element, element_type)?;

                self.verify_type_data_matches(ins.dst_bufref, &[TypeKind::Bufref(element_type)])?;
            }
            InstrData::BufrefRemove(ins) => {
                self.verify_type_data_matches(ins.src_index, &[TypeKind::Prim(PrimType::Int)])?;

                let element_type = self.expect_bufref(ins.src_bufref)?;

                self.verify_type_data_matches(ins.dst_bufref, &[TypeKind::Bufref(element_type)])?;
            }
            InstrData::BufrefTrunc(ins) => {
                self.verify_type_data_matches(ins.new_len, &[TypeKind::Prim(PrimType::Int)])?;

                let element_type = self.expect_bufref(ins.src_bufref)?;

                self.verify_type_data_matches(ins.dst_bufref, &[TypeKind::Bufref(element_type)])?;
            }
            InstrData::BufrefLen(ins) => {
                self.expect_bufref(ins.src_bufref)?;
                self.verify_type_data_matches(ins.dst_len, &[TypeKind::Prim(PrimType::Int)])?;
            }
            InstrData::BufrefGet(ins) => {
                let element_type = self.expect_bufref(ins.src_bufref)?;
                self.verify_type_data_matches(ins.src_index, &[TypeKind::Prim(PrimType::Int)])?;
                self.verify_type_equals(ins.dst_val, element_type)?;
            }
            InstrData::BufrefGetMRef(ins) => {
                let element_type = self.expect_bufref(ins.src_bufref)?;
                self.verify_type_data_matches(ins.src_index, &[TypeKind::Prim(PrimType::Int)])?;
                self.verify_type_data_matches(ins.dst_ref, &[TypeKind::MRef(element_type)])?;
            }
        }
        Ok(())
    }

    fn verify_entry_block_params(&self) -> Result<(), ValidationError> {
        let mut expected_param_types = vec![];
        expected_param_types.extend(
            self.func
                .header
                .param_types
                .iter()
                .map(|&t| t.kind(self.db).clone()),
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

    fn type_of(&self, val: ValId) -> Type<'db> {
        self.func.vals[val].typ
    }

    fn type_data_of(&self, val: ValId) -> &TypeKind<'db> {
        self.func.vals[val].typ.kind(self.db)
    }

    fn verify_type_data_matches(
        &self,
        val: ValId,
        allowed_types: &[TypeKind],
    ) -> Result<(), ValidationError> {
        let typ = self.func.vals[val].typ;
        if !allowed_types.contains(typ.kind(self.db)) {
            return Err(ValidationError::new(format!(
                "expected one of {allowed_types:?}, found {:?}",
                typ.kind(self.db)
            )));
        }
        Ok(())
    }

    fn verify_type_equals(&self, val: ValId, typ: Type<'db>) -> Result<(), ValidationError> {
        let actual_typ = self.func.vals[val].typ;
        if typ != actual_typ {
            return Err(ValidationError::new(format!(
                "wrong type: expected {:?}, found {:?}",
                typ.kind(self.db),
                actual_typ.kind(self.db)
            )));
        }
        Ok(())
    }

    fn verify_basic_block_args(
        &self,
        block: BasicBlockId,
        args: &EntityList<ValId>,
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
        param_types: &[Type<'db>],
        args: &EntityList<ValId>,
    ) -> Result<(), ValidationError> {
        let args = args.as_slice(&self.func.val_lists);

        if param_types.len() != args.len() {
            return Err(ValidationError::new(
                "wrong number of arguments to function",
            ));
        }

        for (param, arg) in param_types.iter().zip(args.iter().copied()) {
            if param != &self.func.vals[arg].typ {
                return Err(ValidationError::new("wrong type as argument to function"));
            }
        }

        Ok(())
    }

    fn verify_func_instance(
        &self,
        func_instance: AbstractFuncInstance<'db>,
    ) -> Result<(), ValidationError> {
        let type_params = func_instance.type_params(self.db, &self.cx);
        let type_args = func_instance.type_args(self.db);

        for (type_param_idx, type_param) in &type_params {
            let type_param_id = TypeParamId {
                idx: type_param_idx,
                scope: func_instance.type_param_scope(self.db),
            };
            let type_arg = *type_args
                .get(&type_param_id)
                .ok_or_else(|| ValidationError::new("missing type argument"))?;

            if !type_param.is_mirage {
                for bound in &type_param.trait_bounds {
                    if !trait_resolution::does_impl_trait(self.db, self.cx, type_arg, *bound) {
                        return Err(ValidationError::new(
                            "could not satisfy trait bound on func call",
                        ));
                    }
                }
            }
        }

        if let MaybeAssocFunc::AssocFunc { trait_, typ, .. } = func_instance.func(self.db)
            && !trait_resolution::does_impl_trait(self.db, self.cx, typ, trait_)
        {
            return Err(ValidationError::new(format!(
                "could not satisfy trait bound [{:?}: {:?}] on assoc func access",
                typ.kind(self.db),
                trait_.trait_(self.db),
            )));
        }

        Ok(())
    }

    #[track_caller]
    fn expect_struct(
        &self,
        val: ValId,
    ) -> Result<(&'db StructTypeData<'db>, &'db TypeArgs<'db>), ValidationError> {
        self.expect_struct_kind(self.type_of(val))
    }

    #[track_caller]
    fn expect_struct_kind(
        &self,
        typ: Type<'db>,
    ) -> Result<(&'db StructTypeData<'db>, &'db TypeArgs<'db>), ValidationError> {
        match typ.kind(self.db) {
            TypeKind::Algebraic(s) => match s.adt.resolve(self.db, self.cx).kind(self.db) {
                AlgebraicTypeKind::Struct(strukt) => Ok((strukt, &s.type_args)),
            },
            _ => Err(ValidationError::new("expected struct type")),
        }
    }

    #[track_caller]
    fn expect_any_ref(&self, val: ValId) -> Result<Type<'db>, ValidationError> {
        match self.type_data_of(val) {
            TypeKind::MRef(t) => Ok(*t),
            _ => Err(ValidationError::new("expected mref or eref")),
        }
    }

    #[track_caller]
    fn expect_bufref(&self, val: ValId) -> Result<Type<'db>, ValidationError> {
        match self.type_data_of(val) {
            TypeKind::Bufref(t) => Ok(*t),
            _ => Err(ValidationError::new("expected bufref")),
        }
    }
}

/// Verifies that a trait_impl is well-formed.
pub fn verify_trait_impl<'db>(
    db: &'db dyn Database,
    cx: Context<'db>,
    trait_impl: TraitImpl<'db>,
) -> Result<(), ValidationError> {
    let trait_instance = trait_impl.data(db).trait_;
    let trait_data = trait_instance.trait_(db).resolve(db, cx).data(db);

    for (assoc_func, binding) in trait_impl.data(db).assoc_func_bindings.iter() {
        if !trait_data.assoc_funcs.is_valid(assoc_func) {
            continue;
        }

        let assoc_func_data = &trait_data.assoc_funcs[assoc_func];

        let Some(binding) = *binding else {
            return Err(ValidationError::new(format!(
                "missing binding for assoc_func '{}'",
                assoc_func_data.name
            )));
        };

        let bound_ret_type = binding.return_type(db, &cx);
        let expected_ret_type = assoc_func_data
            .return_type
            .substitute_type_args(db, trait_instance.type_args(db))
            .substitute_self_type(db, trait_impl.data(db).impl_for_type);

        if bound_ret_type != expected_ret_type {
            return Err(ValidationError::new(format!(
                "return type for assoc func does not match: expected {:?}, found {:?}",
                expected_ret_type.kind(db),
                bound_ret_type.kind(db)
            )));
        }

        if assoc_func_data.param_types.len() != binding.param_types(db, &cx).len() {
            return Err(ValidationError::new(
                "wrong number of parameters for assoc_func binding",
            ));
        }

        for (expected_type, actual_type) in assoc_func_data
            .param_types
            .iter()
            .copied()
            .zip(binding.param_types(db, &cx))
        {
            let expected_type = expected_type
                .substitute_type_args(db, trait_instance.type_args(db))
                .substitute_self_type(db, trait_impl.data(db).impl_for_type);
            if actual_type != expected_type {
                return Err(ValidationError::new(format!(
                    "parameter type for assoc func does not match: expected {:?}, found {:?}",
                    expected_type.kind(db),
                    actual_type.kind(db),
                )));
            }
        }
    }

    Ok(())
}
