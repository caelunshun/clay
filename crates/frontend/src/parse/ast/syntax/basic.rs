use crate::{
    base::syntax::{HasSpan, Span},
    kw,
    parse::{
        ast::{AstGenericParamList, AstNamedSpec, AstTy},
        token::{Ident, TokenStream},
    },
    semantic::syntax::Mutability,
};
use std::rc::Rc;

// === Attributes === //

#[derive(Debug, Clone)]
pub struct AstAttribute {
    pub span: Span,
    pub is_inner: bool,
    pub path: AstBarePath,
    pub args: TokenStream,
}

// === Paths === //

// Bare
#[derive(Debug, Clone)]
pub struct AstBarePath {
    pub span: Span,
    pub parts: Rc<[AstPathPart]>,
}

impl AstBarePath {
    pub fn as_ident(&self) -> Option<Ident> {
        self.parts
            .first()
            .copied()
            .filter(|_| self.parts.len() == 1)
            .and_then(|v| v.ident())
    }
}

// Tree
#[derive(Debug, Clone)]
pub struct AstTreePath {
    pub span: Span,
    pub base: Rc<[AstPathPart]>,
    pub kind: AstTreePathKind,
}

#[derive(Debug, Clone)]
pub enum AstTreePathKind {
    Direct(Option<Ident>),
    Wild(Span),
    Tree(Vec<AstTreePath>),
}

// Expr
#[derive(Debug, Clone)]
pub struct AstQualifiedExprPath {
    pub span: Span,
    pub qualification: Option<Box<AstQualification>>,
    pub rest: AstExprPath,
}

#[derive(Debug, Clone)]
pub struct AstQualification {
    pub span: Span,
    pub self_ty: AstTy,
    pub as_trait: Option<AstNamedSpec>,
}

#[derive(Debug, Clone)]
pub struct AstExprPath {
    pub span: Span,
    pub segments: Rc<[AstExprPathSegment]>,
}

#[derive(Debug, Clone)]
pub struct AstExprPathSegment {
    pub part: AstPathPart,
    pub args: Option<Box<AstGenericParamList>>,
}

// Part
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct AstPathPart {
    raw: Ident,
}

impl HasSpan for AstPathPart {
    fn span(&self) -> Span {
        self.raw.span
    }
}

impl AstPathPart {
    pub fn wrap_raw(raw: Ident) -> Self {
        Self { raw }
    }

    pub fn new_ident(mut ident: Ident) -> Self {
        if Self::wrap_raw(ident).keyword().is_some() {
            ident.raw = true;
        }

        Self::wrap_raw(ident)
    }

    pub fn raw(self) -> Ident {
        self.raw
    }

    pub fn kind(self) -> AstPathPartKind {
        if self.raw.matches_kw(kw!("crate")) {
            return AstPathPartKind::Keyword(self.raw.span, AstPathPartKw::Crate);
        }

        if self.raw.matches_kw(kw!("super")) {
            return AstPathPartKind::Keyword(self.raw.span, AstPathPartKw::Super);
        }

        if self.raw.matches_kw(kw!("self")) {
            return AstPathPartKind::Keyword(self.raw.span, AstPathPartKw::Self_);
        }

        AstPathPartKind::Regular(self.raw)
    }

    pub fn keyword(self) -> Option<AstPathPartKw> {
        self.kind().as_keyword()
    }

    pub fn ident(self) -> Option<Ident> {
        self.kind().as_regular()
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AstPathPartKind {
    Keyword(Span, AstPathPartKw),
    Regular(Ident),
}

impl AstPathPartKind {
    pub fn as_keyword(self) -> Option<AstPathPartKw> {
        match self {
            AstPathPartKind::Keyword(_, kw) => Some(kw),
            _ => None,
        }
    }

    pub fn as_regular(self) -> Option<Ident> {
        match self {
            AstPathPartKind::Regular(ident) => Some(ident),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AstPathPartKw {
    Crate,
    Super,
    Self_,
}

// === Mutability === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AstMutability {
    Mut(Span),
    Ref(Span),
}

impl AstMutability {
    pub fn strip_span(self) -> Mutability {
        match self {
            AstMutability::Mut(..) => Mutability::Mut,
            AstMutability::Ref(..) => Mutability::Not,
        }
    }
}

impl HasSpan for AstMutability {
    fn span(&self) -> Span {
        let (AstMutability::Mut(span) | AstMutability::Ref(span)) = *self;
        span
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AstOptMutability {
    Mut(Span),
    Ref(Span),
    Implicit,
}

impl AstOptMutability {
    pub fn as_explicit(self) -> Option<AstMutability> {
        match self {
            AstOptMutability::Mut(span) => Some(AstMutability::Mut(span)),
            AstOptMutability::Ref(span) => Some(AstMutability::Ref(span)),
            AstOptMutability::Implicit => None,
        }
    }

    pub fn was_explicit(self) -> bool {
        self.as_explicit().is_some()
    }

    pub fn as_muta(self) -> Mutability {
        match self {
            AstOptMutability::Mut(_) => Mutability::Mut,
            AstOptMutability::Ref(_) | AstOptMutability::Implicit => Mutability::Not,
        }
    }
}

// === Visibility === //

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
    PubIn(AstBarePath),
}

impl AstVisibilityKind {
    pub fn is_omitted(&self) -> bool {
        matches!(self, Self::Implicit)
    }
}
