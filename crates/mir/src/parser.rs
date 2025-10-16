use crate::{
    builder::FuncBuilder,
    module::{
        BasicBlock, Context, ContextBuilder, FieldData, FuncHeader, FuncRef, FuncTypeData,
        StructTypeData, TypeRef,
    },
    Func, PrimType, TypeKind, Val,
};
use bumpalo::Bump;
use compact_str::ToCompactString;
use cranelift_entity::PrimaryMap;
use hashbrown::HashMap;
use salsa::Database;
use std::fmt::Display;
use zyon_core::sexpr::{SExpr, SExprRef};
use SExprRef::*;

#[derive(Debug, Clone)]
pub struct ParseError(pub std::string::String);

impl ParseError {
    pub fn new(msg: impl Display) -> Self {
        Self(msg.to_string())
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
        types: Default::default(),
        funcs: Default::default(),
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
    types: HashMap<&'a str, TypeRef>,
    /// Maps function names in the s-expression representation
    /// to their FuncRefs. Note that function headers are initialized
    /// after parse_funcs_initial is called, but implementations
    /// are not yet initialized (FuncRef::resolve will panic) until
    /// after parse_funcs_full is called.
    funcs: HashMap<&'a str, FuncRef>,
}

impl<'a, 'db> Parser<'a, 'db> {
    /// Populates `self.cx` with items from the s-expression.
    pub fn parse_mir(mut self) -> Result<(), ParseError> {
        let items = match self.mir_expr {
            List([Symbol("mir"), items @ ..]) => items,
            _ => return Err(ParseError::new("expected `mir` expression")),
        };

        self.parse_types_initial(items)?;
        self.parse_types_full(items)?;
        self.deduplicate_types();
        self.parse_funcs_initial(items)?;
        self.parse_funcs_full(items)?;

        Ok(())
    }

    /// Initial pass that allocates TypeRefs
    /// for each declared type, but does not
    /// parse the actual types yet. We do this
    /// in two phases to support cyclic types.
    fn parse_types_initial(&mut self, items: &[SExprRef<'a>]) -> Result<(), ParseError> {
        for item in items {
            match item {
                List([Symbol("type"), Symbol(type_name), ..]) => {
                    self.types.insert(*type_name, self.cx.alloc_type());
                }
                _ => continue,
            }
        }
        Ok(())
    }

    /// Initializes all defined types. Must be
    /// called after parse_types_initial.
    fn parse_types_full(&mut self, items: &[SExprRef<'a>]) -> Result<(), ParseError> {
        for item in items {
            match item {
                List([Symbol("type"), Symbol(type_name), type_data]) => {
                    let type_ref = self.parse_type(type_data)?;
                    self.cx.bind_type(
                        self.db,
                        self.types[type_name],
                        type_ref.resolve_in_builder(self.cx),
                    );
                }
                _ => continue,
            }
        }
        Ok(())
    }

    fn parse_type(&mut self, expr: &SExprRef<'a>) -> Result<TypeRef, ParseError> {
        Ok(match expr {
            Symbol(x) if let Some(type_ref) = self.types.get(x) => *type_ref,
            Symbol("int") => self
                .cx
                .get_or_create_type_ref_with_data(self.db, TypeKind::Prim(PrimType::Int)),
            Symbol("real") => self
                .cx
                .get_or_create_type_ref_with_data(self.db, TypeKind::Prim(PrimType::Real)),
            Symbol("byte") => self
                .cx
                .get_or_create_type_ref_with_data(self.db, TypeKind::Prim(PrimType::Byte)),
            Symbol("bool") => self
                .cx
                .get_or_create_type_ref_with_data(self.db, TypeKind::Prim(PrimType::Bool)),
            Symbol("str") => self
                .cx
                .get_or_create_type_ref_with_data(self.db, TypeKind::Prim(PrimType::Str)),
            Symbol("unit") => self
                .cx
                .get_or_create_type_ref_with_data(self.db, TypeKind::Prim(PrimType::Unit)),
            List([Symbol("mref"), pointee_type]) => {
                let pointee_type = self.parse_type(pointee_type)?;
                self.cx
                    .get_or_create_type_ref_with_data(self.db, TypeKind::MRef(pointee_type))
            }
            List([Symbol("eref"), pointee_type]) => {
                let pointee_type = self.parse_type(pointee_type)?;
                self.cx
                    .get_or_create_type_ref_with_data(self.db, TypeKind::ERef(pointee_type))
            }
            List([Symbol("list"), element_type]) => {
                let element_type = self.parse_type(element_type)?;
                self.cx
                    .get_or_create_type_ref_with_data(self.db, TypeKind::List(element_type))
            }
            List([Symbol("func"), decls @ ..]) => {
                let mut return_type = None;
                let mut param_types = Vec::new();
                for decl in decls {
                    match decl {
                        List([Symbol("returns"), expr]) => {
                            return_type = Some(self.parse_type(expr)?);
                        }
                        List([Symbol("param"), expr]) => {
                            param_types.push(self.parse_type(expr)?);
                        }
                        _ => return Err(ParseError::new("invalid declaration in func expr")),
                    }
                }
                self.cx.get_or_create_type_ref_with_data(
                    self.db,
                    TypeKind::Func(FuncTypeData {
                        param_types,
                        return_type: return_type
                            .ok_or_else(|| ParseError::new("missing return type"))?,
                    }),
                )
            }
            List([Symbol("struct"), decls @ ..]) => {
                let mut fields = PrimaryMap::new();
                for decl in decls {
                    match decl {
                        List([Symbol("field"), Symbol(field_name), field_type]) => {
                            fields.push(FieldData {
                                name: field_name.to_compact_string(),
                                typ: self.parse_type(field_type)?,
                            });
                        }
                        _ => return Err(ParseError::new("invalid declaration in struct expr ")),
                    }
                }

                self.cx.get_or_create_type_ref_with_data(
                    self.db,
                    TypeKind::Struct(StructTypeData { fields }),
                )
            }
            _ => return Err(ParseError::new(format!("invalid type {expr:?}"))),
        })
    }

    fn deduplicate_types(&mut self) {
        let mapping = self.cx.deduplicate_types(self.db);
        self.types
            .values_mut()
            .for_each(|type_ref| *type_ref = mapping[*type_ref]);
    }

    fn parse_funcs_initial(&mut self, items: &[SExprRef<'a>]) -> Result<(), ParseError> {
        for item in items {
            match item {
                List([Symbol("func"), Symbol(func_name), decls @ ..]) => {
                    let mut return_type = None;
                    let mut captures_type = None;
                    let mut entry_block = None;
                    let mut blocks = HashMap::new();

                    #[derive(Default)]
                    struct BlockHeader {
                        params: Vec<TypeRef>,
                    }

                    for decl in decls {
                        match decl {
                            List([Symbol("return_type"), expr]) => {
                                return_type = Some(self.parse_type(expr)?);
                            }
                            List([Symbol("captures_type"), expr]) => {
                                captures_type = Some(self.parse_type(expr)?);
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
                            _ => return Err(ParseError::new("invalid decl in func expr")),
                        }
                    }

                    let header = FuncHeader {
                        name: func_name.to_compact_string(),
                        captures_type: captures_type
                            .ok_or_else(|| ParseError::new("missing captures type"))?,
                        param_types: blocks
                            .get(
                                &entry_block
                                    .ok_or_else(|| ParseError::new("missing entry block"))?,
                            )
                            .ok_or_else(|| ParseError::new("entry block not defined"))?
                            .params[1..] // skip captures parameter passed to the entry block
                            .to_vec(),
                        return_type: return_type
                            .ok_or_else(|| ParseError::new("missing return type"))?,
                    };

                    let func_ref = self.cx.alloc_func();
                    self.cx.bind_func_header(func_ref, header);
                    self.funcs.insert(*func_name, func_ref);
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
                    let func_ref = self.funcs[func_name];
                    let header = func_ref.resolve_header(self.db, self.cx).clone();

                    let mut func_builder = FuncBuilder::new(
                        self.db,
                        func_name.to_compact_string(),
                        header.captures_type,
                        header.return_type,
                        self.cx,
                    );
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
                    self.cx.bind_func(func_ref, Func::new(self.db, func));
                }
                _ => continue,
            }
        }
        Ok(())
    }

    fn find_entry_block_name(&self, decls: &[SExprRef<'a>]) -> &'a str {
        for decl in decls {
            if let List([Symbol("entry"), Symbol(block)]) = decl {
                return *block;
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
            _ => return Err(ParseError::new(format!("unknown instruction `{instr}`"))),
        }

        Ok(())
    }
}

struct FuncParserState<'a, 'db> {
    func_builder: FuncBuilder<'db>,
    entry_block_name: &'a str,
    blocks: HashMap<&'a str, BasicBlock>,
    vals: HashMap<&'a str, Val>,
}

impl<'a, 'db> FuncParserState<'a, 'db> {
    pub fn parse_args_unary(&mut self, args: &[SExprRef<'a>]) -> Result<(Val, Val), ParseError> {
        let [Symbol(dst), List([Symbol(src)])] = args else {
            return Err(ParseError::new("invalid instruction arguments"));
        };

        Ok((self.get_or_create_val(dst), self.get_val(src)?))
    }

    pub fn parse_args_binary(
        &mut self,
        args: &[SExprRef<'a>],
    ) -> Result<(Val, Val, Val), ParseError> {
        let [Symbol(dst), List([Symbol(src1), Symbol(src2)])] = args else {
            return Err(ParseError::new("invalid instruction arguments"));
        };

        Ok((
            self.get_or_create_val(dst),
            self.get_val(src1)?,
            self.get_val(src2)?,
        ))
    }

    pub fn get_val(&self, name: &str) -> Result<Val, ParseError> {
        self.vals
            .get(&name)
            .ok_or_else(|| {
                ParseError::new(format!("undefined value `{name}` used as source operand"))
            })
            .copied()
    }

    pub fn get_or_create_val(&mut self, name: &'a str) -> Val {
        *self
            .vals
            .entry(name)
            .or_insert_with(|| self.func_builder.val())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::InstrData;
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
                (captures_type unit)
                (entry block0)
                (block block0
                    (param v0
                        (mref unit))
                    (param v1 int)
                    (int.add v2 (v1 v1)))))
        "#};
        let db = DatabaseImpl::new();
        let input = Input::new(&db, mir);
        let cx = parse_helper(&db, input);
        let cx = cx.data(&db);

        assert_eq!(cx.funcs.len(), 1);

        let func = *cx.funcs.values().next().unwrap();
        let func_data = func.data(&db);

        assert_eq!(func_data.header.param_types, vec![cx.int_type_ref()]);
        assert_eq!(func_data.header.captures_type, cx.unit_type_ref());
        assert_eq!(func_data.basic_blocks.len(), 1);

        let block = &func_data.basic_blocks[func_data.entry_block];

        assert_eq!(block.instrs.len(), 1);
        assert!(matches!(block.instrs[0], InstrData::IntAdd(_)));
    }
}
