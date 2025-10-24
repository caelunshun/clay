use crate::{
    Func, InstrData, PrimType, TypeKind, Val,
    instr::{self, CompareMode},
    module::{BasicBlock, ConstantData, Context, Field, FuncData, Type},
};
use cranelift_entity::EntityRef;
use fir_core::sexpr::{SExpr, float, int, list, string, symbol};
use hashbrown::HashMap;
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
    val_names: HashMap<Val, SExpr>,
    next_val_index: usize,
    basic_block_names: HashMap<BasicBlock, SExpr>,
    next_basic_block_index: usize,
    current_func: Option<Func<'db>>,
}

impl<'db> Formatter<'db> {
    pub fn format_all(mut self) -> SExpr {
        let mut items = vec![symbol("mir")];

        for (_, func) in &self.cx.data(self.db).funcs {
            items.push(self.format_func(*func));
        }

        SExpr::List(items.into_boxed_slice())
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
            TypeKind::Func(f) => {
                let mut items = vec![
                    symbol("func"),
                    list([symbol("returns"), self.format_type(f.return_type)]),
                ];

                for param in &f.param_types {
                    items.push(list([symbol("param"), self.format_type(*param)]));
                }

                SExpr::List(items.into_boxed_slice())
            }
            TypeKind::List(t) => list([symbol("list"), self.format_type(*t)]),
            TypeKind::Algebraic(_) => todo!(),
            TypeKind::TypeParam(_) => todo!(),
            TypeKind::Self_ => symbol("Self"),
        }
    }

    fn format_func(&mut self, func: Func<'db>) -> SExpr {
        self.val_names.clear();
        self.next_val_index = 0;
        self.basic_block_names.clear();
        self.next_basic_block_index = 0;
        self.current_func = Some(func);

        let func_data = func.data(self.db);
        let mut items = vec![
            symbol("func"),
            symbol(func_data.header.name.clone()),
            list([
                symbol("return_type"),
                self.format_type(func_data.header.return_type),
            ]),
            list([
                symbol("captures_type"),
                self.format_type(func_data.header.captures_type),
            ]),
        ];

        items.push(list([
            symbol("entry"),
            self.basic_block_name(func_data.entry_block),
        ]));

        for (block, _) in &func_data.basic_blocks {
            items.push(self.format_block(func_data, block))
        }

        SExpr::List(items.into_boxed_slice())
    }

    fn format_block(&mut self, func_data: &FuncData, block: BasicBlock) -> SExpr {
        let mut items = vec![symbol("block"), self.basic_block_name(block)];

        let block_data = &func_data.basic_blocks[block];

        for &param_val in block_data.params.as_slice(&func_data.val_lists) {
            items.push(list([
                symbol("param"),
                self.val_name(param_val),
                self.format_type(func_data.vals[param_val].typ),
            ]));
        }

        for instr in &block_data.instrs {
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
                    list([
                        symbol(ins.func.data(self.db, self.cx).header.name.clone()),
                        list(args),
                    ]),
                ])
            }
            InstrData::CallIndirect(ins) => {
                let mut args = Vec::new();
                for &arg in ins.args.as_slice(&func_data.val_lists) {
                    args.push(self.val_name(arg));
                }
                list([
                    symbol("call_indirect"),
                    self.val_name(ins.return_value_dst),
                    list([self.val_name(ins.func), list(args)]),
                ])
            }
            InstrData::Return(ins) => {
                list([symbol("return"), list([self.val_name(ins.return_value)])])
            }
            InstrData::Copy(ins) => self.format_instr_unary("copy", ins),
            InstrData::Constant(ins) => {
                let constant = match ins.constant.data(self.db) {
                    ConstantData::Int(x) => int(x),
                    ConstantData::Real(x) => float(x),
                    ConstantData::Bool(x) => symbol(x.to_string()),
                    ConstantData::Str(x) => string(x),
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
                let TypeKind::Struct(strukt) = ins.typ.data(self.db, self.cx) else {
                    panic!("init_struct requires struct type")
                };

                let mut fields = Vec::new();
                for (i, &field) in ins.fields.as_slice(&func_data.val_lists).iter().enumerate() {
                    let field_data = &strukt.fields[Field::new(i)];
                    fields.push(list([
                        symbol("field"),
                        symbol(field_data.name.clone()),
                        self.val_name(field),
                    ]));
                }

                fields.insert(
                    0,
                    self.type_names[&ins.typ.resolve(self.db, self.cx)].clone(),
                );

                list([symbol("struct.init"), self.val_name(ins.dst), list(fields)])
            }
            InstrData::GetField(ins) => {
                let TypeKind::Struct(strukt) =
                    func_data.vals[ins.src_struct].typ.data(self.db, self.cx)
                else {
                    panic!("not a struct type");
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
                let TypeKind::Struct(strukt) =
                    func_data.vals[ins.src_struct].typ.data(self.db, self.cx)
                else {
                    panic!("not a struct type");
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
                let TypeKind::MRef(r) = func_data.vals[ins.src_ref].typ.data(self.db, self.cx)
                else {
                    panic!("not a ref type");
                };
                let TypeKind::Struct(strukt) = r.data(self.db, self.cx) else {
                    panic!("not a struct type");
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
            InstrData::MakeFunctionObject(ins) => list([
                symbol("func.init"),
                self.val_name(ins.dst),
                list([
                    symbol(ins.func.data(self.db, self.cx).header.name.clone()),
                    self.val_name(ins.captures_ref),
                ]),
            ]),
            InstrData::MakeList(ins) => list([
                symbol("list.init"),
                self.val_name(ins.dst),
                list([self.format_type(ins.element_type)]),
            ]),
            InstrData::ListPush(ins) => {
                if let Some(dst_list) = ins.dst_list {
                    list([
                        symbol("list.push"),
                        self.val_name(dst_list),
                        list([self.val_name(ins.src_list), self.val_name(ins.src_element)]),
                    ])
                } else {
                    list([
                        symbol("list.ref.push"),
                        list([self.val_name(ins.src_list), self.val_name(ins.src_element)]),
                    ])
                }
            }
            InstrData::ListRemove(ins) => {
                if let Some(dst_list) = ins.dst_list {
                    list([
                        symbol("list.remove"),
                        self.val_name(dst_list),
                        list([self.val_name(ins.src_list), self.val_name(ins.src_index)]),
                    ])
                } else {
                    list([
                        symbol("list.ref.remove"),
                        list([self.val_name(ins.src_list), self.val_name(ins.src_index)]),
                    ])
                }
            }
            InstrData::ListTrunc(ins) => {
                if let Some(dst_list) = ins.dst_list {
                    list([
                        symbol("list.trunc"),
                        self.val_name(dst_list),
                        list([self.val_name(ins.src_list), self.val_name(ins.new_len)]),
                    ])
                } else {
                    list([
                        symbol("list.ref.trunc"),
                        list([self.val_name(ins.src_list), self.val_name(ins.new_len)]),
                    ])
                }
            }
            InstrData::ListLen(ins) => list([
                symbol("list.len"),
                self.val_name(ins.dst_len),
                list([self.val_name(ins.src_list)]),
            ]),
            InstrData::ListGet(ins) => list([
                symbol("list.get"),
                self.val_name(ins.dst_val),
                list([self.val_name(ins.src_list), self.val_name(ins.src_index)]),
            ]),
            InstrData::ListGetMRef(ins) => list([
                symbol("list.get_mref"),
                self.val_name(ins.dst_ref),
                list([self.val_name(ins.src_list), self.val_name(ins.src_index)]),
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

    fn val_name(&mut self, val: Val) -> SExpr {
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

    fn basic_block_name(&mut self, bb: BasicBlock) -> SExpr {
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
    use crate::{
        builder::FuncBuilder,
        module::{ContextBuilder, FuncRef},
    };
    use fir_core::Db;
    use indoc::indoc;

    #[salsa::tracked]
    fn make_basic_func<'db>(db: &'db dyn Database) -> Context<'db> {
        let mut cx = ContextBuilder::new(db);
        let mut func = FuncBuilder::new(db, "add", Type::unit(db), Type::int(db), &mut cx);
        let param0 = func.append_param(Type::int(db));
        let param1 = func.append_param(Type::int(db));
        let ret_val = func.val();
        func.instr(&mut cx).int_add(ret_val, param0, param1);
        func.instr(&mut cx).return_(ret_val);
        let func = func.build(&mut cx);
        FuncRef::create(db, func, &mut cx);
        Context::new(db, cx.finish())
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
                    (captures_type unit)
                    (entry block0)
                    (block block0
                        (param v0
                            (mref unit))
                        (param v1 int)
                        (param v2 int)
                        (int.add v3
                            (v1 v2))
                        (return
                            (v3)))))
        "#}
        )
    }
}
