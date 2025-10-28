use crate::{base::syntax::Span, parse::token::Ident};

#[derive(Debug, Clone)]
pub struct Module {
    pub outer_span: Span,
    pub inner_span: Span,
    pub name: Ident,
    pub items: Vec<ModuleItem>,
}

#[derive(Debug, Clone)]
pub enum ModuleItem {}
