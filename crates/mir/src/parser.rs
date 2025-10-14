use crate::{module::Module, Func, Type};
use bumpalo::Bump;
use indexmap::IndexSet;
use salsa::Database;
use zyon_core::sexpr::{SExpr, SExprRef};
use SExprRef::*;

/// Decodes an SExpr representation of an MIR module
/// into the internal IR structs.
///
/// Currently, some malformed inputs cause panics.
/// This parser is primarily intended for building
/// test cases, not for production use.
pub fn parse_mir<'db>(db: &'db dyn Database, src: &str) -> Option<Module<'db>> {
    let sexpr = SExpr::parse(src)?;
    let bump = &Bump::new();
    let sexpr = sexpr.to_ref(bump);

    todo!()
}

struct Parser<'a, 'db> {
    db: &'db dyn Database,
    module_expr: SExprRef<'a>,
    types: IndexSet<Type<'db>, hashbrown::DefaultHashBuilder>,
    funcs: Vec<Func<'db>>,
}

impl<'a, 'db> Parser<'a, 'db> {
    pub fn parse_module(mut self) -> Option<Module<'db>> {
        match self.module_expr {
            List([Symbol("module"), List(items)]) => {
                
            }
            _ => return None,
        }

        todo!()
    }
}
