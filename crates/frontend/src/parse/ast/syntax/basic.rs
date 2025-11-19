use crate::{
    base::syntax::Span,
    kw,
    parse::{
        ast::{AstGenericParamList, AstTy},
        token::{Ident, TokenStream},
    },
    semantic::syntax::Mutability,
};
use std::rc::Rc;

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

#[derive(Debug, Clone)]
pub struct AstExprPath {
    pub span: Span,
    pub segments: Rc<[AstExprPathSegment]>,
}

#[derive(Debug, Clone)]
pub struct AstExprPathSegment {
    pub part: Ident,
    pub args: Option<Box<AstGenericParamList>>,
}

#[derive(Debug, Clone)]
pub struct AstExprQualification {
    pub span: Span,
    pub src_ty: AstTy,
    pub as_trait: Option<AstTy>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AstMutability {
    Mut(Span),
    Ref(Span),
    Implicit,
}

impl AstMutability {
    pub fn as_muta(self) -> Mutability {
        match self {
            AstMutability::Mut(_) => Mutability::Mut,
            AstMutability::Ref(_) | AstMutability::Implicit => Mutability::Not,
        }
    }
}

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

impl AstVisibilityKind {
    pub fn is_omitted(&self) -> bool {
        matches!(self, Self::Implicit)
    }
}
