use crate::{
    builder::FuncBuilder,
    module::{
        Context, ContextBuilder, FieldData, FuncHeader, FuncRef, FuncTypeData, StructTypeData,
        TypeRef,
    },
    Func, PrimType, Type, TypeKind,
};
use bumpalo::Bump;
use compact_str::{CompactString, ToCompactString};
use cranelift_entity::PrimaryMap;
use hashbrown::HashMap;
use indexmap::IndexSet;
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

    todo!()
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
            List([Symbol("mir"), List(items)]) => *items,
            _ => return Err(ParseError::new("expected `mir` expression")),
        };

        self.parse_types_initial(items)?;
        self.parse_types_full(items)?;
        self.deduplicate_types();

        todo!()
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
                    let header = func_ref.resolve_header(self.db, self.cx);

                    for decl in decls {
                        match decl {
                            List([Symbol("block"), Symbol(block_name), block_decls @ ..]) => {}
                            _ => continue,
                        }
                    }
                }
                _ => continue,
            }
        }
        Ok(())
    }
}

struct BlockParser<'db> {
    db: &'db dyn Database,
    func_builder: FuncBuilder<'db>,
}
