use crate::{base::syntax::Span, parse::token::Ident};

#[derive(Debug, Clone)]
pub struct Func {
    pub span: Span,
    pub name: Ident,
    // TODO
}
