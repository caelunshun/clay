use crate::{
    Func, InstrData, PrimType, TypeKind, ValId,
    ir::{
        AbstractFuncInstance, AlgebraicType, AlgebraicTypeKind, BasicBlockId, ConstantValue,
        Context, FieldId, FuncData, MaybeAssocFunc, Trait, TraitImpl, TraitInstance, Type,
        TypeArgs, TypeParams,
        instr::{self, CompareMode},
    },
};
use cranelift_entity::EntityRef;
use fir_core::{
    HashMap,
    sexpr::{SExpr, float, int, list, string, symbol},
};
use salsa::Database;

/// Converts an mir Context and all its contents to an S-expression.
#[salsa::tracked]
pub fn format_context<'db>(db: &'db dyn Database, cx: Context<'db>) -> SExpr {
    Formatter {
        db,
        cx,
        val_names: Default::default(),
        next_val_index: 0,
        basic_block_names: Default::default(),
        next_basic_block_index: 0,
        current_func: None,
    }
    .format_all()
}

struct Formatter<'db> {
    db: &'db dyn Database,
    cx: Context<'db>,
    val_names: HashMap<ValId, SExpr>,
    next_val_index: usize,
    basic_block_names: HashMap<BasicBlockId, SExpr>,
    next_basic_block_index: usize,
    current_func: Option<Func<'db>>,
}

impl<'db> Formatter<'db> {
    pub fn format_all(mut self) -> SExpr {
        let mut items = vec![symbol("mir")];

        for (_, adt) in &self.cx.data(self.db).adts {
            items.push(self.format_adt(*adt));
        }

        for (_, trait_) in &self.cx.data(self.db).traits {
            items.push(self.format_trait(*trait_));
        }

        for (_, trait_impl) in &self.cx.data(self.db).trait_impls {
            items.push(self.format_trait_impl(*trait_impl));
        }

        for (_, func) in &self.cx.data(self.db).funcs {
            items.push(self.format_func(*func));
        }

        SExpr::List(items.into_boxed_slice())
    }

    fn format_trait(&self, trait_: Trait<'db>) -> SExpr {
        let data = trait_.data(self.db);

        let mut items = vec![symbol("trait"), symbol(data.name.clone())];
        items.extend(self.format_type_params(&data.type_params));

        for assoc_func in data.assoc_funcs.values() {
            let mut assoc_func_items = vec![symbol("assoc_func"), symbol(assoc_func.name.clone())];

            assoc_func_items.extend(self.format_type_params(&assoc_func.type_params));

            for &param_type in &assoc_func.param_types {
                assoc_func_items.push(list([symbol("param"), self.format_type(param_type)]));
            }

            assoc_func_items.push(list([
                symbol("return_type"),
                self.format_type(assoc_func.return_type),
            ]));

            items.push(list(assoc_func_items));
        }

        list(items)
    }

    fn format_trait_impl(&self, trait_impl: TraitImpl<'db>) -> SExpr {
        let data = trait_impl.data(self.db);
        let trait_data = data
            .trait_
            .trait_(self.db)
            .resolve(self.db, self.cx)
            .data(self.db);

        let mut items = vec![symbol("trait_impl")];

        items.extend(self.format_type_params(&data.type_params));

        items.push(list([
            symbol("trait"),
            self.format_trait_instance(data.trait_),
        ]));
        items.push(list([symbol("type"), self.format_type(data.impl_for_type)]));

        for (assoc_func, func_binding) in data.assoc_func_bindings.iter() {
            if let Some(func_binding) = func_binding {
                items.push(list([
                    symbol("assoc_func"),
                    symbol(trait_data.assoc_funcs[assoc_func].name.clone()),
                    self.format_func_instance(*func_binding),
                ]));
            }
        }

        list(items)
    }

    fn format_adt(&self, adt: AlgebraicType<'db>) -> SExpr {
        let mut decls = Vec::new();

        decls.extend(self.format_type_params(adt.type_params(self.db)));

        match adt.kind(self.db) {
            AlgebraicTypeKind::Struct(struct_data) => {
                let mut struct_decls = vec![symbol("struct")];

                for (_, field) in &struct_data.fields {
                    struct_decls.push(list([
                        symbol("field"),
                        symbol(field.name.clone()),
                        self.format_type(field.typ),
                    ]));
                }

                decls.push(list(struct_decls));
            }
        }

        let mut items = vec![symbol("adt"), symbol(adt.name(self.db).clone())];
        items.extend(decls);
        list(items)
    }

    fn format_type(&self, typ: Type<'db>) -> SExpr {
        match typ.kind(self.db) {
            TypeKind::Prim(p) => match *p {
                PrimType::Int => symbol("int"),
                PrimType::Real => symbol("real"),
                PrimType::Byte => symbol("byte"),
                PrimType::Bool => symbol("bool"),
                PrimType::Str => symbol("str"),
                PrimType::Unit => symbol("unit"),
            },
            TypeKind::MRef(p) => list([symbol("mref"), self.format_type(*p)]),
            TypeKind::Bufref(t) => list([symbol("bufref"), self.format_type(*t)]),
            TypeKind::Algebraic(adt_instance) => {
                let name = adt_instance
                    .adt
                    .resolve(self.db, self.cx)
                    .name(self.db)
                    .clone();
                if adt_instance.type_args.is_empty() {
                    symbol(name)
                } else {
                    let mut items = vec![symbol(name)];
                    items.extend(self.format_type_args(&adt_instance.type_args));
                    list(items)
                }
            }
            TypeKind::TypeParam(param) => symbol(param.resolve(self.db, &self.cx).name.clone()),
            TypeKind::Self_ => symbol("Self"),
        }
    }

    fn format_type_params(&self, type_params: &TypeParams<'db>) -> Vec<SExpr> {
        let mut items = Vec::new();

        for (_, type_param) in type_params {
            let mut param_items = vec![symbol("type_param"), symbol(type_param.name.clone())];

            if type_param.is_mirage {
                param_items.push(symbol("mirage"));
            }
            if type_param.is_assoc_type {
                param_items.push(symbol("assoc_type"));
            }

            for &bound in &type_param.trait_bounds {
                param_items.push(list([
                    symbol("requires"),
                    self.format_trait_instance(bound),
                ]));
            }

            items.push(list(param_items));
        }

        items
    }

    fn format_trait_instance(&self, trait_instance: TraitInstance<'db>) -> SExpr {
        let name = trait_instance
            .trait_(self.db)
            .resolve(self.db, self.cx)
            .data(self.db)
            .name
            .clone();

        if trait_instance.type_args(self.db).is_empty() {
            return symbol(name);
        }

        let mut items = vec![symbol(name)];
        items.extend(self.format_type_args(trait_instance.type_args(self.db)));
        list(items)
    }

    fn format_func_instance(&self, func_instance: AbstractFuncInstance<'db>) -> SExpr {
        match func_instance.func(self.db) {
            MaybeAssocFunc::Func(func_id) => {
                let name = symbol(func_id.resolve_header(self.db, &self.cx).name.clone());

                if func_instance.type_args(self.db).is_empty() {
                    name
                } else {
                    let mut items = vec![name];
                    items.extend(self.format_type_args(func_instance.type_args(self.db)));
                    list(items)
                }
            }
            MaybeAssocFunc::AssocFunc {
                trait_,
                typ,
                assoc_func,
            } => {
                let mut items = vec![
                    symbol("assoc_func"),
                    self.format_type(typ),
                    self.format_trait_instance(trait_),
                    symbol(
                        trait_
                            .trait_(self.db)
                            .resolve(self.db, self.cx)
                            .data(self.db)
                            .assoc_funcs[assoc_func]
                            .name
                            .clone(),
                    ),
                ];
                items.extend(self.format_type_args(func_instance.type_args(self.db)));

                list(items)
            }
        }
    }

    fn format_type_args(&self, type_args: &TypeArgs<'db>) -> Vec<SExpr> {
        let mut items = Vec::new();

        for (type_param, arg) in type_args.iter() {
            let name = type_param.resolve(self.db, &self.cx).name.clone();
            items.push(list([
                symbol("type_arg"),
                symbol(name),
                self.format_type(*arg),
            ]));
        }

        items
    }

    fn format_func(&mut self, func: Func<'db>) -> SExpr {
        self.val_names.clear();
        self.next_val_index = 0;
        self.basic_block_names.clear();
        self.next_basic_block_index = 0;
        self.current_func = Some(func);

        let func_data = func.data(self.db);
        let mut items = vec![symbol("func"), symbol(func_data.header.name.clone())];
        items.extend(self.format_type_params(&func_data.header.type_params));
        items.push(list([
            symbol("return_type"),
            self.format_type(func_data.header.return_type),
        ]));

        items.push(list([
            symbol("entry"),
            self.basic_block_name(func_data.entry_block),
        ]));

        for (block, _) in &func_data.basic_blocks {
            items.push(self.format_block(func_data, block))
        }

        SExpr::List(items.into_boxed_slice())
    }

    fn format_block(&mut self, func_data: &FuncData<'db>, block: BasicBlockId) -> SExpr {
        let mut items = vec![symbol("block"), self.basic_block_name(block)];

        let block_data = &func_data.basic_blocks[block];

        for &param_val in block_data.params.as_slice(&func_data.val_lists) {
            items.push(list([
                symbol("param"),
                self.val_name(param_val),
                self.format_type(func_data.vals[param_val].typ),
            ]));
        }

        for (_, instr) in &block_data.instrs {
            items.push(self.format_instr(func_data, instr));
        }

        SExpr::List(items.into_boxed_slice())
    }

    fn format_instr(&mut self, func_data: &FuncData, instr: &InstrData) -> SExpr {
        match instr {
            InstrData::Jump(ins) => {
                let mut args = Vec::new();
                for &arg in ins.args.as_slice(&func_data.val_lists) {
                    args.push(self.val_name(arg));
                }
                list([
                    symbol("jump"),
                    list([self.basic_block_name(ins.target), list(args)]),
                ])
            }
            InstrData::Branch(ins) => {
                let mut args_true = Vec::new();
                for &arg in ins.args_true.as_slice(&func_data.val_lists) {
                    args_true.push(self.val_name(arg));
                }

                let mut args_false = Vec::new();
                for &arg in ins.args_false.as_slice(&func_data.val_lists) {
                    args_false.push(self.val_name(arg));
                }

                list([
                    symbol("branch"),
                    list([
                        self.val_name(ins.condition),
                        list([
                            symbol("true"),
                            self.basic_block_name(ins.target_true),
                            list(args_true),
                        ]),
                        list([
                            symbol("false"),
                            self.basic_block_name(ins.target_false),
                            list(args_false),
                        ]),
                    ]),
                ])
            }
            InstrData::Call(ins) => {
                let mut args = Vec::new();
                for &arg in ins.args.as_slice(&func_data.val_lists) {
                    args.push(self.val_name(arg));
                }
                list([
                    symbol("call"),
                    self.val_name(ins.return_value_dst),
                    list([self.format_func_instance(ins.func), list(args)]),
                ])
            }
            InstrData::Return(ins) => {
                list([symbol("return"), list([self.val_name(ins.return_value)])])
            }
            InstrData::Copy(ins) => self.format_instr_unary("copy", ins),
            InstrData::Constant(ins) => {
                let constant = match ins.constant.value(self.db) {
                    ConstantValue::Int(x) => int(*x),
                    ConstantValue::Real(x) => float(*x),
                    ConstantValue::Bool(x) => symbol(x.to_string()),
                    ConstantValue::Str(x) => string(x.clone()),
                };
                list([symbol("constant"), self.val_name(ins.dst), list([constant])])
            }
            InstrData::IntAdd(ins) => self.format_instr_binary("int.add", ins),
            InstrData::IntSub(ins) => self.format_instr_binary("int.sub", ins),
            InstrData::IntMul(ins) => self.format_instr_binary("int.mul", ins),
            InstrData::IntDiv(ins) => self.format_instr_binary("int.div", ins),
            InstrData::IntCmp(ins) => self.format_instr_cmp("int.cmp", ins),
            InstrData::RealAdd(ins) => self.format_instr_binary("real.add", ins),
            InstrData::RealSub(ins) => self.format_instr_binary("real.sub", ins),
            InstrData::RealMul(ins) => self.format_instr_binary("real.mul", ins),
            InstrData::RealDiv(ins) => self.format_instr_binary("real.div", ins),
            InstrData::RealCmp(ins) => self.format_instr_cmp("real.cmp", ins),
            InstrData::RealToInt(ins) => self.format_instr_unary("real.to_int", ins),
            InstrData::IntToReal(ins) => self.format_instr_unary("int.to_real", ins),
            InstrData::ByteToInt(ins) => self.format_instr_unary("byte.to_int", ins),
            InstrData::IntToByte(ins) => self.format_instr_unary("int.to_byte", ins),
            InstrData::BoolAnd(ins) => self.format_instr_binary("bool.and", ins),
            InstrData::BoolOr(ins) => self.format_instr_binary("bool.or", ins),
            InstrData::BoolXor(ins) => self.format_instr_binary("bool.xor", ins),
            InstrData::BoolNot(ins) => self.format_instr_unary("bool.not", ins),
            InstrData::InitStruct(ins) => {
                let TypeKind::Algebraic(adt_instance) = ins.typ.kind(self.db) else {
                    panic!("struct.init requires struct type")
                };
                let adt = adt_instance.adt.resolve(self.db, self.cx);
                let AlgebraicTypeKind::Struct(strukt) = adt.kind(self.db) else {
                    panic!("struct.init requires struct type")
                };

                let mut fields = Vec::new();
                for (i, &field) in ins.fields.as_slice(&func_data.val_lists).iter().enumerate() {
                    let field_data = &strukt.fields[FieldId::new(i)];
                    fields.push(list([
                        symbol("field"),
                        symbol(field_data.name.clone()),
                        self.val_name(field),
                    ]));
                }

                fields.insert(0, self.format_type(ins.typ));

                list([symbol("struct.init"), self.val_name(ins.dst), list(fields)])
            }
            InstrData::GetField(ins) => {
                let TypeKind::Algebraic(adt_instance) =
                    func_data.vals[ins.src_struct].typ.kind(self.db)
                else {
                    panic!("struct.init requires struct type")
                };
                let adt = adt_instance.adt.resolve(self.db, self.cx);
                let AlgebraicTypeKind::Struct(strukt) = adt.kind(self.db) else {
                    panic!("struct.init requires struct type")
                };

                list([
                    symbol("struct.get"),
                    self.val_name(ins.dst),
                    list([
                        self.val_name(ins.src_struct),
                        symbol(strukt.fields[ins.field].name.clone()),
                    ]),
                ])
            }
            InstrData::SetField(ins) => {
                let TypeKind::Algebraic(adt_instance) =
                    func_data.vals[ins.src_struct].typ.kind(self.db)
                else {
                    panic!("struct.init requires struct type")
                };
                let adt = adt_instance.adt.resolve(self.db, self.cx);
                let AlgebraicTypeKind::Struct(strukt) = adt.kind(self.db) else {
                    panic!("struct.init requires struct type")
                };

                list([
                    symbol("struct.set"),
                    self.val_name(ins.dst_struct),
                    list([
                        self.val_name(ins.src_struct),
                        symbol(strukt.fields[ins.field].name.clone()),
                        self.val_name(ins.src_field_val),
                    ]),
                ])
            }
            InstrData::Alloc(ins) => list([
                symbol("alloc"),
                self.val_name(ins.dst_ref),
                list([self.val_name(ins.src)]),
            ]),
            InstrData::Load(ins) => list([
                symbol("load"),
                self.val_name(ins.dst),
                list([self.val_name(ins.src_ref)]),
            ]),
            InstrData::Store(ins) => list([
                symbol("store"),
                list([self.val_name(ins.val), self.val_name(ins.ref_)]),
            ]),
            InstrData::MakeFieldMRef(ins) => {
                let TypeKind::MRef(r) = func_data.vals[ins.src_ref].typ.kind(self.db) else {
                    panic!("not a ref type");
                };
                let TypeKind::Algebraic(adt_instance) = r.kind(self.db) else {
                    panic!("struct.init requires struct type")
                };
                let adt = adt_instance.adt.resolve(self.db, self.cx);
                let AlgebraicTypeKind::Struct(strukt) = adt.kind(self.db) else {
                    panic!("struct.init requires struct type")
                };

                list([
                    symbol("struct.get_mref"),
                    self.val_name(ins.dst_ref),
                    list([
                        self.val_name(ins.src_ref),
                        symbol(strukt.fields[ins.field].name.clone()),
                    ]),
                ])
            }
            InstrData::MakeBufref(ins) => list([
                symbol("bufref.init"),
                self.val_name(ins.dst),
                list([self.format_type(ins.element_type)]),
            ]),
            InstrData::BufrefPush(ins) => list([
                symbol("bufref.push"),
                self.val_name(ins.dst_bufref),
                list([
                    self.val_name(ins.src_bufref),
                    self.val_name(ins.src_element),
                ]),
            ]),
            InstrData::BufrefRemove(ins) => list([
                symbol("bufref.remove"),
                self.val_name(ins.dst_bufref),
                list([self.val_name(ins.src_bufref), self.val_name(ins.src_index)]),
            ]),
            InstrData::BufrefTrunc(ins) => list([
                symbol("bufref.trunc"),
                self.val_name(ins.dst_bufref),
                list([self.val_name(ins.src_bufref), self.val_name(ins.new_len)]),
            ]),
            InstrData::BufrefLen(ins) => list([
                symbol("bufref.len"),
                self.val_name(ins.dst_len),
                list([self.val_name(ins.src_bufref)]),
            ]),
            InstrData::BufrefGet(ins) => list([
                symbol("bufref.get"),
                self.val_name(ins.dst_val),
                list([self.val_name(ins.src_bufref), self.val_name(ins.src_index)]),
            ]),
            InstrData::BufregGetMRef(ins) => list([
                symbol("bufref.get_mref"),
                self.val_name(ins.dst_ref),
                list([self.val_name(ins.src_bufref), self.val_name(ins.src_index)]),
            ]),
        }
    }

    fn format_instr_unary(&mut self, name: &str, instr: &instr::Unary) -> SExpr {
        list([
            symbol(name),
            self.val_name(instr.dst),
            list([self.val_name(instr.src)]),
        ])
    }

    fn format_instr_binary(&mut self, name: &str, instr: &instr::Binary) -> SExpr {
        list([
            symbol(name),
            self.val_name(instr.dst),
            list([self.val_name(instr.src1), self.val_name(instr.src2)]),
        ])
    }

    fn format_instr_cmp(&mut self, name: &str, instr: &instr::Cmp) -> SExpr {
        let mode = symbol(match instr.mode {
            CompareMode::Less => "<",
            CompareMode::LessOrEqual => "<=",
            CompareMode::Greater => ">",
            CompareMode::GreaterOrEqual => ">=",
            CompareMode::Equal => "==",
            CompareMode::NotEqual => "!=",
        });
        list([
            symbol(name),
            self.val_name(instr.dst),
            list([mode, self.val_name(instr.src1), self.val_name(instr.src2)]),
        ])
    }

    fn val_name(&mut self, val: ValId) -> SExpr {
        self.val_names
            .entry(val)
            .or_insert_with(|| {
                if let Some(name) = &self.current_func.unwrap().data(self.db).vals[val].name {
                    symbol(name.clone())
                } else {
                    let name = symbol(format!("v{}", self.next_val_index));
                    self.next_val_index += 1;
                    name
                }
            })
            .clone()
    }

    fn basic_block_name(&mut self, bb: BasicBlockId) -> SExpr {
        self.basic_block_names
            .entry(bb)
            .or_insert_with(|| {
                if let Some(name) = &self.current_func.unwrap().data(self.db).basic_blocks[bb].name
                {
                    symbol(name.clone())
                } else {
                    let name = symbol(format!("block{}", self.next_basic_block_index));
                    self.next_basic_block_index += 1;
                    name
                }
            })
            .clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{builder::FuncBuilder, ir::ContextBuilder};
    use fir_core::Db;
    use indoc::indoc;
    use pretty_assertions::assert_eq;

    #[salsa::tracked]
    fn make_basic_func<'db>(db: &'db dyn Database) -> Context<'db> {
        let mut cx = ContextBuilder::new();
        let mut func = FuncBuilder::new(db, "add", Type::int(db), &mut cx);
        let param0 = func.append_param(Type::int(db));
        let param1 = func.append_param(Type::int(db));
        let ret_val = func.val();
        func.instr(&mut cx).int_add(ret_val, param0, param1);
        func.instr(&mut cx).return_(ret_val);
        let func = func.build(&mut cx);
        let func_id = cx.alloc_func();
        cx.bind_func(func_id, Func::new(db, func));
        cx.finish(db)
    }

    #[test]
    fn basic_formatting() {
        let db = Db::default();
        let cx = make_basic_func(&db);
        let formatted = format_context(&db, cx).to_string();
        assert_eq!(
            formatted,
            indoc! {r#"
            (mir
                (func add
                    (return_type int)
                    (entry block0)
                    (block block0
                        (param v0 int)
                        (param v1 int)
                        (int.add v2
                            (v0 v1))
                        (return
                            (v2)))))
        "#}
        )
    }
}
