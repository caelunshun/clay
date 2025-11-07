use crate::{
    base::{
        ErrorGuaranteed,
        syntax::{Span, HasSpan},
    },
    kw,
    parse::token::{Ident, Lifetime, TokenStream},
};
use std::rc::Rc;

// === Item === //

#[derive(Debug, Clone)]
pub enum AstItem {
    Mod(AstItemModule),
    Use(AstItemUse),
    Trait(AstItemTrait),
    Impl(AstItemImpl),
    Error(AstItemBase, ErrorGuaranteed),
}

impl AstItem {
    pub fn base(&self) -> &AstItemBase {
        let (AstItem::Mod(AstItemModule { base, .. })
        | AstItem::Use(AstItemUse { base, .. })
        | AstItem::Trait(AstItemTrait { base, .. })
        | AstItem::Impl(AstItemImpl { base, .. })
        | AstItem::Error(base, ..)) = self;

        base
    }
}

#[derive(Debug, Clone)]
pub struct AstItemBase {
    pub span: Span,
    pub outer_attrs: Vec<AstAttribute>,
    pub vis: AstVisibility,
}

#[derive(Debug, Clone)]
pub struct AstItemModule {
    pub base: AstItemBase,
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
    pub base: AstItemBase,
    pub path: AstUsePath,
}

#[derive(Debug, Clone)]
pub struct AstItemTrait {
    pub base: AstItemBase,
    pub name: Ident,
    pub generics: Option<AstGenericParamList>,
    pub inherits: Option<AstTraitClauseList>,
    pub body: AstImplLikeBody,
}

#[derive(Debug, Clone)]
pub struct AstItemImpl {
    pub base: AstItemBase,
    pub generics: Option<AstGenericParamList>,
    pub first_ty: AstTy,
    pub second_ty: Option<AstTy>,
    pub body: AstImplLikeBody,
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

impl AstSimplePath {
    pub fn as_ident(&self) -> Option<Ident> {
        self.parts.first().copied().filter(|v| {
            self.parts.len() == 1
                && !v.matches_kw(kw!("crate"))
                && !v.matches_kw(kw!("super"))
                && !v.matches_kw(kw!("self"))
        })
    }
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
pub struct AstNamedSpec {
    pub span: Span,
    pub path: AstSimplePath,
    pub params: Option<AstGenericParamList>,
}

#[derive(Debug, Clone)]
pub struct AstTraitClauseList {
    pub span: Span,
    pub clauses: Vec<Result<AstTraitClause, ErrorGuaranteed>>,
}

#[derive(Debug, Clone)]
pub enum AstTraitClause {
    Outlives(Lifetime),
    Trait(AstNamedSpec),
}

#[derive(Debug, Clone)]
pub struct AstGenericParamList {
    pub span: Span,
    pub list: Vec<AstGenericParam>,
}

#[derive(Debug, Clone)]
pub struct AstGenericParam {
    pub span: Span,
    pub kind: AstGenericParamKind,
}

#[derive(Debug, Clone)]
pub enum AstGenericParamKind {
    /// A bare type (e.g. `u32`, `(u32, &'a i32)?`).
    PositionalTy(AstTy),

    /// A bare region (e.g. `'a`, `'_`)
    PositionalRe(Lifetime),

    /// A name with a clause list (e.g. `MyAssoc: Foo + Bar`, `T: 'gc`).
    InheritTy(Ident, AstTraitClauseList),

    /// A region with a clause list (e.g. `'a: 'b + 'c`).
    InheritRe(Lifetime, AstTraitClauseList),

    /// A name with an equality to a type (e.g. `MyAssoc = u32`).
    TyEquals(Ident, AstTy),
}

#[derive(Debug, Clone)]
pub enum AstGenericDef<'a> {
    Ty(Ident, Option<&'a AstTraitClauseList>),
    Re(Lifetime, Option<&'a AstTraitClauseList>),
}

impl AstGenericParamKind {
    pub fn as_generic_def(&self) -> Option<AstGenericDef<'_>> {
        match self {
            AstGenericParamKind::PositionalTy(ty) => {
                ty.as_ident().map(|ident| AstGenericDef::Ty(ident, None))
            }
            AstGenericParamKind::PositionalRe(re) => Some(AstGenericDef::Re(*re, None)),
            AstGenericParamKind::InheritTy(ident, clauses) => {
                Some(AstGenericDef::Ty(*ident, Some(clauses)))
            }
            AstGenericParamKind::InheritRe(re, clauses) => {
                Some(AstGenericDef::Re(*re, Some(clauses)))
            }
            AstGenericParamKind::TyEquals(..) => None,
        }
    }
}

// === Types === //

#[derive(Debug, Clone)]
pub enum AstTyOrRe {
    Re(Lifetime),
    Ty(AstTy),
}

impl HasSpan for AstTyOrRe {
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
    Name(AstSimplePath, Option<AstGenericParamList>),
    Reference(Option<Lifetime>, Box<AstTy>),
    Trait(AstTraitClauseList),
    Tuple(Vec<AstTy>),
    Option(Box<AstTy>),
    Infer,
    Error(ErrorGuaranteed),
}

impl AstTy {
    pub fn as_ident(&self) -> Option<Ident> {
        match &self.kind {
            AstTyKind::Name(path, list) if list.is_none() => path.as_ident(),
            _ => None,
        }
    }
}

// === Impl-like Bodies === //

#[derive(Debug, Clone)]
pub struct AstImplLikeBody {
    pub span: Span,
    pub members: Vec<AstImplLikeMember>,
}

#[derive(Debug, Clone)]
pub struct AstImplLikeMember {
    pub span: Span,
    pub vis: AstVisibility,
    pub kind: AstImplLikeMemberKind,
}

#[derive(Debug, Clone)]
pub enum AstImplLikeMemberKind {
    TypeEquals(Ident, AstTy),
    TypeInherits(Ident, AstTraitClauseList),
    Error(ErrorGuaranteed),
}
