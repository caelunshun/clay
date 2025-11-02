use crate::{
    base::{
        ErrorGuaranteed,
        syntax::{Span, Spanned},
    },
    parse::token::{Ident, Lifetime, TokenStream},
};
use std::rc::Rc;

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
    Use(AstItemUse),
    Trait(AstItemTrait),
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
pub struct AstItemUse {
    pub path: AstUsePath,
}

#[derive(Debug, Clone)]
pub struct AstItemTrait {
    pub name: Ident,
    pub generics: Option<AstGenericDefList>,
    pub members: Vec<AstTraitMember>,
}

#[derive(Debug, Clone)]
pub struct AstTraitMember {
    pub span: Span,
    pub kind: AstTraitMemberKind,
}

#[derive(Debug, Clone)]
pub enum AstTraitMemberKind {
    AssocType(Ident, AstTraitClauseList),
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
    PubIn(AstSimplePath),
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
    pub parts: Rc<[Ident]>,
}

#[derive(Debug, Clone)]
pub struct AstUsePath {
    pub span: Span,
    pub base: Rc<[Ident]>,
    pub kind: AstUsePathKind,
}

#[derive(Debug, Clone)]
pub enum AstUsePathKind {
    Direct(Option<Ident>),
    Wild(Span),
    Tree(Vec<AstUsePath>),
}

// === Clauses === //

#[derive(Debug, Clone)]
pub struct AstGenericDefList {
    pub span: Span,
    pub defs: Vec<Result<AstGenericDef, ErrorGuaranteed>>,
}

#[derive(Debug, Clone)]
pub struct AstGenericDef {
    pub span: Span,
    pub kind: AstGenericDefKind,
    pub clauses: Option<AstTraitClauseList>,
}

#[derive(Debug, Clone)]
pub enum AstGenericDefKind {
    Lifetime(Lifetime),
    Type(Ident),
}

#[derive(Debug, Clone)]
pub struct AstTraitClauseList {
    pub span: Span,
    pub clauses: Vec<Result<AstTraitClause, ErrorGuaranteed>>,
}

#[derive(Debug, Clone)]
pub enum AstTraitClause {
    Outlives(Lifetime),
    Trait(AstTraitSpec),
}

#[derive(Debug, Clone)]
pub struct AstTraitSpec {
    pub span: Span,
    pub path: AstSimplePath,
    pub params: Option<AstTraitParamList>,
}

#[derive(Debug, Clone)]
pub struct AstTraitParamList {
    pub span: Span,
    pub list: Vec<AstTraitParam>,
}

#[derive(Debug, Clone)]
pub struct AstTraitParam {
    pub span: Span,
    pub kind: AstTraitParamKind,
}

#[derive(Debug, Clone)]
pub enum AstTraitParamKind {
    PositionalEquals(AstTyOrRe),
    NamedEquals(Ident, AstTy),
    NamedUnspecified(Ident, AstTraitClauseList),
}

// === Types === //

#[derive(Debug, Clone)]
pub enum AstTyOrRe {
    Re(Lifetime),
    Ty(AstTy),
}

impl Spanned for AstTyOrRe {
    fn span(&self) -> Span {
        match self {
            AstTyOrRe::Re(v) => v.span,
            AstTyOrRe::Ty(v) => v.span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AstTy {
    pub span: Span,
    pub kind: AstTyKind,
}

#[derive(Debug, Clone)]
pub enum AstTyKind {
    This,
    Name(AstSimplePath, Option<AstTraitParamList>),
    Reference(Option<Lifetime>, Box<AstTy>),
    Trait(AstTraitSpec),
    Tuple(Vec<AstTy>),
    Option(Box<AstTy>),
    Infer,
    Error(ErrorGuaranteed),
}
