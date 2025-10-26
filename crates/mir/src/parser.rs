use crate::{
    Func, TypeKind, ValId,
    builder::FuncBuilder,
    ir::{
        AlgebraicType, AlgebraicTypeId, AlgebraicTypeInstance, AlgebraicTypeKind, AssocFunc,
        BasicBlockId, Constant, ConstantValue, Context, ContextBuilder, Field, FuncHeader, FuncId,
        FuncInstance, MaybeAssocFunc, StructTypeData, Trait, TraitData, TraitId, TraitInstance,
        Type, TypeArgs, TypeParam, TypeParamId, TypeParamIndex, TypeParamScope, TypeParams,
        instr::CompareMode,
    },
};
use SExprRef::*;
use bumpalo::Bump;
use compact_str::ToCompactString;
use cranelift_entity::{EntityRef, PrimaryMap};
use fir_core::{
    HashMap,
    sexpr::{SExpr, SExprRef},
};
use salsa::Database;
use std::{fmt::Display, panic::Location};

#[derive(Debug, Clone)]
pub struct ParseError(pub std::string::String, pub &'static Location<'static>);

impl ParseError {
    #[track_caller]
    pub fn new(msg: impl Display) -> Self {
        Self(msg.to_string(), Location::caller())
    }
}

/// Decodes an SExpr representation of an MIR module
/// into the internal IR structs.
///
/// Currently, some malformed inputs cause panics.
/// This parser is primarily intended for building
/// test cases, not for production use.
pub fn parse_mir<'db>(db: &'db dyn Database, src: &str) -> Result<Context<'db>, ParseError> {
    let sexpr = SExpr::parse(src).ok_or_else(|| ParseError::new("invalid s-expression"))?;
    let bump = &Bump::new();
    let sexpr = sexpr.to_ref(bump);

    let mut cx = ContextBuilder::new(db);
    let parser = Parser {
        db,
        cx: &mut cx,
        mir_expr: sexpr,
        adts: Default::default(),
        funcs: Default::default(),
        traits: Default::default(),
        type_params: Default::default(),
        current_type_param_scopes: Default::default(),
    };
    parser.parse_mir()?;

    Ok(Context::new(db, cx.finish()))
}

struct Parser<'a, 'db> {
    db: &'db dyn Database,
    cx: &'a mut ContextBuilder<'db>,
    mir_expr: SExprRef<'a>,

    /// Maps type names in the s-expression representation
    /// to their TypeRefs. Note that types aren't initialized
    /// (TypeRef::resolve will panic) until after parse_types_full
    /// is called.
    adts: HashMap<&'a str, AlgebraicTypeId>,
    /// Maps function names in the s-expression representation
    /// to their FuncRefs. Note that function headers are initialized
    /// after parse_funcs_initial is called, but implementations
    /// are not yet initialized (FuncRef::resolve will panic) until
    /// after parse_funcs_full is called.
    funcs: HashMap<&'a str, FuncId>,
    traits: HashMap<&'a str, TraitId>,
    /// Maps type parameter scopes and the corresponding type parameter
    /// names to type parameter IDs.
    type_params: HashMap<(TypeParamScope, &'a str), TypeParamId>,

    /// TypeParamScopes accessible in the current scope being parsed.
    current_type_param_scopes: Vec<TypeParamScope>,
}

impl<'a, 'db> Parser<'a, 'db> {
    /// Populates `self.cx` with items from the s-expression.
    pub fn parse_mir(mut self) -> Result<(), ParseError> {
        let items = match self.mir_expr {
            List([Symbol("mir"), items @ ..]) => items,
            _ => return Err(ParseError::new("expected `mir` expression")),
        };

        self.parse_traits_initial(items)?;
        self.parse_adts_initial(items)?;
        self.parse_funcs_initial(items)?;
        self.parse_traits_full(items)?;
        self.parse_adts_full(items)?;
        self.parse_funcs_full(items)?;

        assert!(self.current_type_param_scopes.is_empty());

        Ok(())
    }

    /// Initial pass that allocates TraitIds for each declared
    /// trait, and determines the type parameter names of each trait,
    /// but does not parse the trait definitions yet. We do this
    /// in two phases to support cycles.
    fn parse_traits_initial(&mut self, items: &[SExprRef<'a>]) -> Result<(), ParseError> {
        for item in items {
            if let List([Symbol("trait"), Symbol(trait_name), decls @ ..]) = item {
                let trait_id = self.cx.alloc_trait();
                self.traits.insert(*trait_name, trait_id);

                self.parse_type_params_initial(decls, TypeParamScope::Trait(trait_id))?;
            }
        }
        Ok(())
    }

    fn parse_traits_full(&mut self, items: &[SExprRef<'a>]) -> Result<(), ParseError> {
        for item in items {
            if let List([Symbol("trait"), Symbol(trait_name), decls @ ..]) = item {
                let trait_id = self.get_trait(trait_name)?;

                let tp_scope = TypeParamScope::Trait(trait_id);
                self.push_type_param_scope(tp_scope);
                let type_params = self.parse_type_params(decls, tp_scope)?;
                let mut assoc_funcs = PrimaryMap::new();

                for decl in decls {
                    match decl {
                        List(
                            [
                                Symbol("assoc_func"),
                                Symbol(assoc_func_name),
                                assoc_func_decls @ ..,
                            ],
                        ) => {
                            let assoc_func_id = assoc_funcs.next_key();

                            let tp_scope = TypeParamScope::AssocFunc(trait_id, assoc_func_id);
                            self.parse_type_params_initial(assoc_func_decls, tp_scope)?;

                            self.push_type_param_scope(tp_scope);

                            let type_params = self.parse_type_params(assoc_func_decls, tp_scope)?;

                            let mut param_types = Vec::new();
                            let mut return_type = None;
                            for assoc_func_decl in assoc_func_decls {
                                match assoc_func_decl {
                                    List([Symbol("return_type"), ret_type_expr]) => {
                                        return_type = Some(self.parse_type(ret_type_expr)?);
                                    }
                                    List([Symbol("param"), param_type]) => {
                                        param_types.push(self.parse_type(param_type)?);
                                    }
                                    // Already parsed by parse_type_params
                                    List([Symbol("type_param"), ..]) => {}
                                    _ => return Err(ParseError::new("invalid decl in assoc func")),
                                }
                            }

                            assoc_funcs.push(AssocFunc {
                                name: assoc_func_name.to_compact_string(),
                                type_params,
                                param_types,
                                return_type: return_type.ok_or_else(|| {
                                    ParseError::new("missing return type for assoc func")
                                })?,
                            });

                            self.pop_type_param_scope(tp_scope);
                        }
                        // Already parsed by parse_type_params
                        List([Symbol("type_param"), ..]) => {}
                        _ => return Err(ParseError::new("invalid decl in trait")),
                    }
                }

                self.cx.bind_trait(
                    trait_id,
                    Trait::new(
                        self.db,
                        TraitData {
                            name: trait_name.to_compact_string(),
                            type_params,
                            assoc_funcs,
                        },
                    ),
                );

                self.pop_type_param_scope(tp_scope);
            }
        }
        Ok(())
    }

    /// Initial pass that allocates AlgebraicTypeIds
    /// for each declared type, but does not
    /// parse the actual types yet. We do this
    /// in two phases to support cyclic types.
    fn parse_adts_initial(&mut self, items: &[SExprRef<'a>]) -> Result<(), ParseError> {
        for item in items {
            match item {
                List([Symbol("adt"), Symbol(type_name), ..]) => {
                    self.adts.insert(*type_name, self.cx.alloc_adt());
                }
                _ => continue,
            }
        }
        Ok(())
    }

    /// Initializes all defined types. Must be
    /// called after parse_types_initial.
    fn parse_adts_full(&mut self, items: &[SExprRef<'a>]) -> Result<(), ParseError> {
        for item in items {
            match item {
                List([Symbol("adt"), Symbol(type_name), type_data]) => {
                    let adt = self.parse_adt(type_data)?;
                    self.cx.bind_adt(
                        self.db,
                        self.adts[type_name],
                        AlgebraicType::new(
                            self.db,
                            type_name.to_compact_string(),
                            Default::default(),
                            adt,
                        ),
                    );
                }
                _ => continue,
            }
        }
        Ok(())
    }

    fn parse_adt(&mut self, expr: &SExprRef<'a>) -> Result<AlgebraicTypeKind<'db>, ParseError> {
        match expr {
            List([Symbol("struct"), decls @ ..]) => {
                let mut fields = PrimaryMap::new();

                for decl in decls {
                    let List([Symbol("field"), Symbol(field_name), field_typ]) = decl else {
                        return Err(ParseError::new("invalid decl in struct"));
                    };
                    fields.push(Field {
                        name: field_name.to_compact_string(),
                        typ: self.parse_type(field_typ)?,
                    });
                }

                Ok(AlgebraicTypeKind::Struct(StructTypeData { fields }))
            }
            _ => Err(ParseError::new("invalid ADT")),
        }
    }

    fn parse_type(&mut self, expr: &SExprRef<'a>) -> Result<Type<'db>, ParseError> {
        Ok(match expr {
            Symbol(type_param_name)
                if let Some(type_param) = self.search_type_param(type_param_name) =>
            {
                Type::new(self.db, TypeKind::TypeParam(type_param))
            }
            Symbol(adt_name) if let Some(adt) = self.adts.get(adt_name) => Type::new(
                self.db,
                TypeKind::Algebraic(AlgebraicTypeInstance {
                    adt: *adt,
                    type_args: Default::default(),
                }),
            ),
            Symbol("int") => Type::int(self.db),
            Symbol("real") => Type::real(self.db),
            Symbol("byte") => Type::byte(self.db),
            Symbol("bool") => Type::bool(self.db),
            Symbol("str") => Type::str(self.db),
            Symbol("unit") => Type::unit(self.db),
            List([Symbol("mref"), pointee_type]) => {
                let pointee_type = self.parse_type(pointee_type)?;
                Type::new(self.db, TypeKind::MRef(pointee_type))
            }
            List([Symbol("list"), element_type]) => {
                let element_type = self.parse_type(element_type)?;
                Type::new(self.db, TypeKind::List(element_type))
            }

            _ => return Err(ParseError::new(format!("invalid type {expr:?}"))),
        })
    }

    /// Populates self.type_params with type parameter ID mappings,
    /// but does not parse the parameters yet.
    fn parse_type_params_initial(
        &mut self,
        items: &[SExprRef<'a>],
        scope: TypeParamScope,
    ) -> Result<(), ParseError> {
        let mut idx = 0;
        for decl in items {
            if let List([Symbol("type_param"), Symbol(name), ..]) = decl {
                self.type_params.insert(
                    (scope, *name),
                    TypeParamId {
                        scope,
                        idx: TypeParamIndex::new(idx),
                    },
                );
                idx += 1;
            }
        }
        Ok(())
    }

    fn parse_type_params(
        &mut self,
        items: &[SExprRef<'a>],
        scope: TypeParamScope,
    ) -> Result<TypeParams<'db>, ParseError> {
        let mut type_params = TypeParams::new();

        for decl in items {
            if let List([Symbol("type_param"), Symbol(name), type_param_decls @ ..]) = decl {
                let mut is_assoc_type = false;
                let mut is_mirage = false;
                let mut trait_bounds = Vec::new();

                for type_param_decl in type_param_decls {
                    match type_param_decl {
                        Symbol("mirage") => is_mirage = true,
                        Symbol("assoc_type") => is_assoc_type = true,
                        List([Symbol("requires"), trait_instance]) => {
                            trait_bounds.push(self.parse_trait_instance(trait_instance)?);
                        }
                        _ => return Err(ParseError::new("unknown decl in type param")),
                    }
                }

                let idx = type_params.push(TypeParam {
                    is_assoc_type,
                    is_mirage,
                    trait_bounds,
                    name: name.to_compact_string(),
                });
                assert_eq!(self.type_params[&(scope, *name)].idx, idx);
            }
        }

        Ok(type_params)
    }

    fn parse_trait_instance(
        &mut self,
        expr: &SExprRef<'a>,
    ) -> Result<TraitInstance<'db>, ParseError> {
        match expr {
            Symbol(trait_name) => Ok(TraitInstance::new(
                self.db,
                self.get_trait(trait_name)?,
                TypeArgs::default(),
            )),
            _ => todo!(),
        }
    }

    fn parse_funcs_initial(&mut self, items: &[SExprRef<'a>]) -> Result<(), ParseError> {
        for item in items {
            match item {
                List([Symbol("func"), Symbol(func_name), decls @ ..]) => {
                    let func_id = self.cx.alloc_func();

                    self.parse_type_params_initial(decls, TypeParamScope::Func(func_id))?;
                    self.push_type_param_scope(TypeParamScope::Func(func_id));

                    let mut return_type = None;
                    let mut entry_block = None;
                    let mut blocks = HashMap::default();

                    #[derive(Default)]
                    struct BlockHeader<'db> {
                        params: Vec<Type<'db>>,
                    }

                    for decl in decls {
                        match decl {
                            List([Symbol("return_type"), expr]) => {
                                return_type = Some(self.parse_type(expr)?);
                            }
                            List([Symbol("entry"), Symbol(entry)]) => {
                                entry_block = Some(entry.to_owned());
                            }
                            List([Symbol("block"), Symbol(block_name), block_decls @ ..]) => {
                                // Only parse parameters, not instructions,
                                // in this pass.
                                // Parameter types need to be known so
                                // that we can determine the function header.
                                let mut block_header = BlockHeader::default();

                                for decl in block_decls {
                                    match decl {
                                        List([Symbol("param"), _, param_type]) => {
                                            block_header.params.push(self.parse_type(param_type)?);
                                        }
                                        _ => continue,
                                    }
                                }

                                blocks.insert(*block_name, block_header);
                            }
                            // already parsed by parse_type_params
                            List([Symbol("type_param"), ..]) => {}
                            _ => return Err(ParseError::new("invalid decl in func expr")),
                        }
                    }

                    let header = FuncHeader {
                        name: func_name.to_compact_string(),
                        param_types: blocks
                            .get(
                                &entry_block
                                    .ok_or_else(|| ParseError::new("missing entry block"))?,
                            )
                            .ok_or_else(|| ParseError::new("entry block not defined"))?
                            .params
                            .clone(),
                        return_type: return_type
                            .ok_or_else(|| ParseError::new("missing return type"))?,
                        type_params: Default::default(),
                    };

                    self.cx.bind_func_header(func_id, header);
                    self.funcs.insert(*func_name, func_id);

                    self.pop_type_param_scope(TypeParamScope::Func(func_id));
                }
                _ => continue,
            }
        }

        Ok(())
    }

    fn parse_funcs_full(&mut self, items: &[SExprRef<'a>]) -> Result<(), ParseError> {
        for item in items {
            match item {
                List([Symbol("func"), Symbol(func_name), decls @ ..]) => {
                    let func_id = self.funcs[func_name];
                    let header = func_id.resolve_header(self.db, self.cx).clone();

                    self.push_type_param_scope(TypeParamScope::Func(func_id));

                    let type_params =
                        self.parse_type_params(decls, TypeParamScope::Func(func_id))?;

                    let mut func_builder = FuncBuilder::new(
                        self.db,
                        func_name.to_compact_string(),
                        header.return_type,
                        self.cx,
                    );
                    for type_param in type_params.values() {
                        func_builder.append_type_param(type_param.clone());
                    }
                    for &param in &header.param_types {
                        func_builder.append_param(param);
                    }

                    let mut state = FuncParserState {
                        func_builder,
                        entry_block_name: self.find_entry_block_name(decls),
                        blocks: Default::default(),
                        vals: Default::default(),
                    };

                    self.parse_blocks_initial(decls, &mut state)?;
                    self.parse_blocks_full(decls, &mut state)?;

                    let func = state.func_builder.build(self.cx);
                    self.cx.bind_func(func_id, Func::new(self.db, func));

                    self.pop_type_param_scope(TypeParamScope::Func(func_id));
                }
                _ => continue,
            }
        }
        Ok(())
    }

    fn find_entry_block_name(&self, decls: &[SExprRef<'a>]) -> &'a str {
        for decl in decls {
            if let List([Symbol("entry"), Symbol(block)]) = decl {
                return block;
            }
        }
        unreachable!()
    }

    fn parse_blocks_initial(
        &mut self,
        decls: &[SExprRef<'a>],
        state: &mut FuncParserState<'a, 'db>,
    ) -> Result<(), ParseError> {
        for decl in decls {
            match decl {
                List([Symbol("block"), Symbol(block_name), block_decls @ ..]) => {
                    let is_entry = *block_name == state.entry_block_name;

                    let block = if is_entry {
                        state.func_builder.entry_block()
                    } else {
                        state.func_builder.create_block()
                    };
                    state.func_builder.set_block_name(block, *block_name);
                    state.func_builder.switch_to_block(block);
                    state.blocks.insert(*block_name, block);

                    let mut i = 0;
                    for block_decl in block_decls {
                        if let List([Symbol("param"), Symbol(val_name), typ]) = block_decl {
                            let typ = self.parse_type(typ)?;
                            let val = if is_entry {
                                state.func_builder.block_param(i)
                            } else {
                                state.func_builder.append_block_param(typ)
                            };
                            state.func_builder.set_val_name(val, *val_name);
                            state.vals.insert(*val_name, val);
                            i += 1;
                        }
                    }
                }
                _ => continue,
            }
        }

        Ok(())
    }

    fn parse_blocks_full(
        &mut self,
        decls: &[SExprRef<'a>],
        state: &mut FuncParserState<'a, 'db>,
    ) -> Result<(), ParseError> {
        for decl in decls {
            if let List([Symbol("block"), Symbol(block_name), block_decls @ ..]) = decl {
                let block = state.blocks[*block_name];
                state.func_builder.switch_to_block(block);
                for block_decl in block_decls {
                    if !matches!(block_decl, List([Symbol("param"), ..])) {
                        self.parse_instr(block_decl, state)?;
                    }
                }
            }
        }

        Ok(())
    }

    fn parse_instr(
        &mut self,
        expr: &SExprRef<'a>,
        state: &mut FuncParserState<'a, 'db>,
    ) -> Result<(), ParseError> {
        let List([Symbol(instr), args @ ..]) = expr else {
            return Err(ParseError::new(format!("invalid block decl {expr:?}")));
        };

        match *instr {
            "jump" => {
                let [List([Symbol(block), List(block_args)])] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let block = state.get_block(block)?;
                let args = state.get_val_list(block_args)?;
                state
                    .func_builder
                    .instr(self.cx)
                    .jump_with_args(block, args)
            }
            "branch" => {
                let [
                    List(
                        [
                            Symbol(condition),
                            List([Symbol("true"), Symbol(block_true), List(args_true)]),
                            List([Symbol("false"), Symbol(block_false), List(args_false)]),
                        ],
                    ),
                ] = args
                else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let condition = state.get_val(condition)?;
                let block_true = state.get_block(block_true)?;
                let block_false = state.get_block(block_false)?;
                let args_true = state.get_val_list(args_true)?;
                let args_false = state.get_val_list(args_false)?;
                state.func_builder.instr(self.cx).branch_with_args(
                    condition,
                    block_true,
                    args_true,
                    block_false,
                    args_false,
                );
            }
            "call" => {
                let [Symbol(dst), List([Symbol(func), List(args)])] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let dst = state.get_or_create_val(dst);
                let func = self
                    .funcs
                    .get(func)
                    .ok_or_else(|| ParseError::new(format!("undefined func `{func}`")))?;
                let args = state.get_val_list(args)?;
                state.func_builder.instr(self.cx).call(
                    dst,
                    FuncInstance::new(self.db, MaybeAssocFunc::Func(*func), TypeArgs::new()),
                    args,
                );
            }
            "return" => {
                let [List([Symbol(return_value)])] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let return_value = state.get_val(return_value)?;
                state.func_builder.instr(self.cx).return_(return_value);
            }
            "copy" => {
                let (dst, src) = state.parse_args_unary(args)?;
                state.func_builder.instr(self.cx).copy(dst, src);
            }
            "constant" => {
                let [Symbol(dst), List([constant])] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let dst = state.get_or_create_val(dst);
                let constant = match constant {
                    Int(x) => ConstantValue::Int(*x),
                    Float(x) => ConstantValue::Real(*x),
                    String(s) => ConstantValue::Str(s.to_compact_string()),
                    Symbol("true") => ConstantValue::Bool(true),
                    Symbol("false") => ConstantValue::Bool(false),
                    _ => return Err(ParseError::new("invalid constant")),
                };
                let constant = Constant::new(self.db, constant);
                state.func_builder.instr(self.cx).constant(dst, constant);
            }
            "int.add" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).int_add(dst, src1, src2);
            }
            "int.sub" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).int_sub(dst, src1, src2);
            }
            "int.mul" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).int_mul(dst, src1, src2);
            }
            "int.div" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).int_div(dst, src1, src2);
            }
            "int.cmp" => {
                let (dst, src1, src2, mode) = state.parse_args_cmp(args)?;
                state
                    .func_builder
                    .instr(self.cx)
                    .int_cmp(dst, src1, src2, mode);
            }
            "real.add" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).real_add(dst, src1, src2);
            }
            "real.sub" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).real_sub(dst, src1, src2);
            }
            "real.mul" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).real_mul(dst, src1, src2);
            }
            "real.div" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).real_div(dst, src1, src2);
            }
            "real.cmp" => {
                let (dst, src1, src2, mode) = state.parse_args_cmp(args)?;
                state
                    .func_builder
                    .instr(self.cx)
                    .real_cmp(dst, src1, src2, mode);
            }
            "real.to_int" => {
                let (dst, src) = state.parse_args_unary(args)?;
                state.func_builder.instr(self.cx).real_to_int(dst, src);
            }
            "int.to_real" => {
                let (dst, src) = state.parse_args_unary(args)?;
                state.func_builder.instr(self.cx).int_to_real(dst, src);
            }
            "byte.to_int" => {
                let (dst, src) = state.parse_args_unary(args)?;
                state.func_builder.instr(self.cx).byte_to_int(dst, src);
            }
            "int.to_byte" => {
                let (dst, src) = state.parse_args_unary(args)?;
                state.func_builder.instr(self.cx).int_to_byte(dst, src);
            }
            "bool.and" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).bool_and(dst, src1, src2);
            }
            "bool.or" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).bool_or(dst, src1, src2);
            }
            "bool.xor" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).bool_xor(dst, src1, src2);
            }
            "bool.not" => {
                let (dst, src) = state.parse_args_unary(args)?;
                state.func_builder.instr(self.cx).bool_not(dst, src);
            }
            "struct.init" => {
                let [Symbol(dst), List([struct_type, fields @ ..])] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let dst = state.get_or_create_val(dst);
                let struct_type = self.parse_type(struct_type)?;
                let TypeKind::Algebraic(adt_instance) = struct_type.kind(self.db) else {
                    return Err(ParseError::new("not a struct type"));
                };
                let AlgebraicTypeKind::Struct(struct_type_data) =
                    adt_instance.adt.resolve(self.db, &self.cx).kind(self.db);

                let mut fields = fields
                    .iter()
                    .map(|field| {
                        let List([Symbol("field"), Symbol(field_name), Symbol(val)]) = field else {
                            return Err(ParseError::new("invalid struct fields"));
                        };
                        let field = struct_type_data
                            .fields
                            .iter()
                            .find(|(_, f)| f.name == field_name)
                            .ok_or_else(|| ParseError::new("undefined field"))?
                            .0;
                        Ok((field, state.get_val(val)?))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                fields.sort_by_key(|(f, _)| *f);
                state.func_builder.instr(self.cx).init_struct(
                    dst,
                    struct_type,
                    fields.into_iter().map(|(_, v)| v),
                );
            }
            "struct.get" => {
                let [Symbol(dst), List([Symbol(src), Symbol(field_name)])] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let dst = state.get_or_create_val(dst);
                let src = state.get_val(src)?;
                let src_type = state.func_builder.val_type(src);
                let TypeKind::Algebraic(adt_instance) = src_type.kind(self.db) else {
                    return Err(ParseError::new("not a struct type"));
                };
                let AlgebraicTypeKind::Struct(struct_type_data) =
                    adt_instance.adt.resolve(self.db, &self.cx).kind(self.db);

                let field = struct_type_data
                    .fields
                    .iter()
                    .find(|(_, f)| f.name == field_name)
                    .ok_or_else(|| ParseError::new("undefined field"))?;

                state
                    .func_builder
                    .instr(self.cx)
                    .get_field(dst, src, field.0);
            }
            "struct.set" => {
                let [
                    Symbol(dst),
                    List([Symbol(src), Symbol(field_name), Symbol(field_val)]),
                ] = args
                else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let dst = state.get_or_create_val(dst);
                let src = state.get_val(src)?;
                let field_val = state.get_val(field_val)?;
                let src_type = state.func_builder.val_type(src);
                let TypeKind::Algebraic(adt_instance) = src_type.kind(self.db) else {
                    return Err(ParseError::new("not a struct type"));
                };
                let AlgebraicTypeKind::Struct(struct_type_data) =
                    adt_instance.adt.resolve(self.db, &self.cx).kind(self.db);

                let field = struct_type_data
                    .fields
                    .iter()
                    .find(|(_, f)| f.name == field_name)
                    .ok_or_else(|| ParseError::new("undefined field"))?;

                state
                    .func_builder
                    .instr(self.cx)
                    .set_field(dst, src, field_val, field.0);
            }
            "alloc" => {
                let (dst, src) = state.parse_args_unary(args)?;
                state.func_builder.instr(self.cx).alloc(dst, src);
            }
            "load" => {
                let (dst, src) = state.parse_args_unary(args)?;
                state.func_builder.instr(self.cx).load(dst, src);
            }
            "store" => {
                let [Symbol(val), Symbol(ref_)] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let ref_ = state.get_val(ref_)?;
                let val = state.get_val(val)?;
                state.func_builder.instr(self.cx).store(ref_, val);
            }
            "struct.get_mref" => {
                let [Symbol(dst), List([Symbol(src), Symbol(field_name)])] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let dst = state.get_or_create_val(dst);
                let src = state.get_val(src)?;
                let src_type = state.func_builder.val_type(src);
                let TypeKind::MRef(pointee) = src_type.kind(self.db) else {
                    return Err(ParseError::new("not a reference to a struct type"));
                };
                let TypeKind::Algebraic(adt_instance) = pointee.kind(self.db) else {
                    return Err(ParseError::new("not a struct type"));
                };
                let AlgebraicTypeKind::Struct(struct_type_data) =
                    adt_instance.adt.resolve(self.db, &self.cx).kind(self.db);

                let field = struct_type_data
                    .fields
                    .iter()
                    .find(|(_, f)| f.name == field_name)
                    .ok_or_else(|| ParseError::new("undefined field"))?;

                state
                    .func_builder
                    .instr(self.cx)
                    .make_field_mref(dst, src, field.0);
            }
            "list.init" => {
                let [Symbol(dst), List([element_type])] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let dst = state.get_or_create_val(dst);
                let element_type = self.parse_type(element_type)?;
                state
                    .func_builder
                    .instr(self.cx)
                    .make_list(dst, element_type);
            }
            "list.push" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).list_push(dst, src1, src2);
            }
            "list.ref.push" => {
                let [List([Symbol(src1), Symbol(src2)])] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let src1 = state.get_val(src1)?;
                let src2 = state.get_val(src2)?;
                state.func_builder.instr(self.cx).list_ref_push(src1, src2);
            }
            "list.remove" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state
                    .func_builder
                    .instr(self.cx)
                    .list_remove(dst, src1, src2);
            }
            "list.ref.remove" => {
                let [List([Symbol(src1), Symbol(src2)])] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let src1 = state.get_val(src1)?;
                let src2 = state.get_val(src2)?;
                state
                    .func_builder
                    .instr(self.cx)
                    .list_ref_remove(src1, src2);
            }
            "list.trunc" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state
                    .func_builder
                    .instr(self.cx)
                    .list_trunc(dst, src1, src2);
            }
            "list.ref.trunc" => {
                let [List([Symbol(src1), Symbol(src2)])] = args else {
                    return Err(ParseError::new("invalid instr arguments"));
                };
                let src1 = state.get_val(src1)?;
                let src2 = state.get_val(src2)?;
                state.func_builder.instr(self.cx).list_ref_trunc(src1, src2);
            }
            "list.len" => {
                let (dst, src) = state.parse_args_unary(args)?;
                state.func_builder.instr(self.cx).list_len(dst, src);
            }
            "list.get" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state.func_builder.instr(self.cx).list_get(dst, src1, src2);
            }
            "list.get_mref" => {
                let (dst, src1, src2) = state.parse_args_binary(args)?;
                state
                    .func_builder
                    .instr(self.cx)
                    .list_get_mref(dst, src1, src2);
            }
            _ => return Err(ParseError::new(format!("unknown instruction `{instr}`"))),
        }

        Ok(())
    }

    fn get_trait(&self, name: &str) -> Result<TraitId, ParseError> {
        self.traits
            .get(&name)
            .copied()
            .ok_or_else(|| ParseError::new(format!("unknown trait `{name}`")))
    }

    fn push_type_param_scope(&mut self, scope: TypeParamScope) {
        self.current_type_param_scopes.push(scope);
    }

    fn pop_type_param_scope(&mut self, scope: TypeParamScope) {
        assert_eq!(self.current_type_param_scopes.pop(), Some(scope));
    }

    /// Searches for a named type parameter in the current
    /// set of type parameter scopes.
    fn search_type_param(&self, name: &str) -> Option<TypeParamId> {
        self.current_type_param_scopes
            .iter()
            .rev() // prefer top of scope stack
            .find_map(|scope| self.type_params.get(&(*scope, name)).copied())
    }
}

struct FuncParserState<'a, 'db> {
    func_builder: FuncBuilder<'db>,
    entry_block_name: &'a str,
    blocks: HashMap<&'a str, BasicBlockId>,
    vals: HashMap<&'a str, ValId>,
}

impl<'a, 'db> FuncParserState<'a, 'db> {
    pub fn parse_args_unary(
        &mut self,
        args: &[SExprRef<'a>],
    ) -> Result<(ValId, ValId), ParseError> {
        let [Symbol(dst), List([Symbol(src)])] = args else {
            return Err(ParseError::new("invalid instruction arguments"));
        };

        Ok((self.get_or_create_val(dst), self.get_val(src)?))
    }

    pub fn parse_args_binary(
        &mut self,
        args: &[SExprRef<'a>],
    ) -> Result<(ValId, ValId, ValId), ParseError> {
        let [Symbol(dst), List([Symbol(src1), Symbol(src2)])] = args else {
            return Err(ParseError::new("invalid instruction arguments"));
        };

        Ok((
            self.get_or_create_val(dst),
            self.get_val(src1)?,
            self.get_val(src2)?,
        ))
    }

    pub fn parse_args_cmp(
        &mut self,
        args: &[SExprRef<'a>],
    ) -> Result<(ValId, ValId, ValId, CompareMode), ParseError> {
        let [
            Symbol(dst),
            List([Symbol(mode), Symbol(src1), Symbol(src2)]),
        ] = args
        else {
            return Err(ParseError::new("invalid instruction arguments"));
        };

        let mode = match *mode {
            "<" => CompareMode::Less,
            "<=" => CompareMode::LessOrEqual,
            ">" => CompareMode::Greater,
            ">=" => CompareMode::GreaterOrEqual,
            "==" => CompareMode::Equal,
            "!=" => CompareMode::NotEqual,
            _ => return Err(ParseError::new("invalid compare mode")),
        };

        Ok((
            self.get_or_create_val(dst),
            self.get_val(src1)?,
            self.get_val(src2)?,
            mode,
        ))
    }

    pub fn get_val(&self, name: &str) -> Result<ValId, ParseError> {
        self.vals
            .get(&name)
            .ok_or_else(|| {
                ParseError::new(format!("undefined value `{name}` used as source operand"))
            })
            .copied()
    }

    pub fn get_or_create_val(&mut self, name: &'a str) -> ValId {
        *self
            .vals
            .entry(name)
            .or_insert_with(|| self.func_builder.named_val(name))
    }

    pub fn get_block(&self, name: &str) -> Result<BasicBlockId, ParseError> {
        self.blocks
            .get(&name)
            .ok_or_else(|| ParseError::new(format!("undefined block `{name}`")))
            .copied()
    }

    pub fn get_val_list(&self, vals: &[SExprRef<'a>]) -> Result<Vec<ValId>, ParseError> {
        vals.iter()
            .map(|val| {
                let Symbol(val) = val else {
                    return Err(ParseError::new("expected value"));
                };
                self.get_val(val)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{InstrData, ir::Type};
    use indoc::indoc;
    use salsa::DatabaseImpl;

    #[salsa::input]
    struct Input {
        src: &'static str,
    }

    #[salsa::tracked]
    fn parse_helper<'db>(db: &'db dyn Database, input: Input) -> Context<'db> {
        parse_mir(db, input.src(db)).unwrap()
    }

    #[test]
    fn parse_simple_mir() {
        let mir = indoc! {r#"
        (mir
            (func foo
                (return_type int)
                (entry block0)
                (block block0
                    (param v1 int)
                    (int.add v2 (v1 v1))
                    (return (v2)))))
        "#};
        let db = DatabaseImpl::new();
        let input = Input::new(&db, mir);
        let cx = parse_helper(&db, input);
        let cx = cx.data(&db);

        assert_eq!(cx.funcs.len(), 1);

        let func = *cx.funcs.values().next().unwrap();
        let func_data = func.data(&db);

        assert_eq!(func_data.header.param_types, vec![Type::int(&db)]);
        assert_eq!(func_data.header.return_type, Type::int(&db));
        assert_eq!(func_data.basic_blocks.len(), 1);

        let block = &func_data.basic_blocks[func_data.entry_block];

        assert_eq!(block.instrs.len(), 2);
        assert!(matches!(block.instrs[0], InstrData::IntAdd(_)));
        assert!(matches!(block.instrs[1], InstrData::Return(_)));
    }
}
