use crate::{
    base::{ErrorGuaranteed, syntax::Span},
    parse::token::{Ident, Lifetime, TokenStream},
};

// === Item === //

#[derive(Debug, Clone)]
pub struct AstItem {
    pub span: Span,
    pub outer_attrs: Vec<AstAttribute>,
    pub vis: AstVisibility,
    pub kind: AstItemKind,
}

#[derive(Debug, Clone)]
pub enum AstItemKind {
    Mod(AstItemModule),
    Error(ErrorGuaranteed),
}

#[derive(Debug, Clone)]
pub struct AstItemModule {
    pub name: Ident,
    pub contents: Option<AstItemModuleContents>,
}

#[derive(Debug, Clone)]
pub struct AstItemModuleContents {
    pub inner_attrs: Vec<AstAttribute>,
    pub items: Vec<AstItem>,
}

#[derive(Debug, Clone)]
pub struct AstItemTrait {
    pub name: Ident,
}

// === Item Helpers === //

#[derive(Debug, Clone)]
pub struct AstVisibility {
    pub span: Span,
    pub kind: AstVisibilityKind,
}

#[derive(Debug, Clone)]
pub enum AstVisibilityKind {
    Implicit,
    Priv,
    Pub,
    PubIn(Vec<AstSimplePath>),
}

#[derive(Debug, Clone)]
pub struct AstAttribute {
    pub span: Span,
    pub is_inner: bool,
    pub path: AstSimplePath,
    pub args: TokenStream,
}

#[derive(Debug, Clone)]
pub struct AstSimplePath {
    pub span: Span,
    pub parts: Vec<Ident>,
}

// === Clauses === //

#[derive(Debug, Clone)]
pub struct AstGenericDef {
    pub span: Span,
    pub name: Ident,
    pub clauses: AstTraitClauseList,
}

#[derive(Debug, Clone)]
pub struct AstTraitClauseList {
    pub span: Span,
    pub clauses: Vec<AstTraitClause>,
}

#[derive(Debug, Clone)]
pub struct AstTraitClause {
    pub span: Span,
    pub kind: AstTraitClauseKind,
}

#[derive(Debug, Clone)]
pub enum AstTraitClauseKind {
    Outlives(Lifetime),
    Trait(),
}
