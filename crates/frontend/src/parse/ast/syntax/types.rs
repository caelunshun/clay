use crate::{
    base::{
        ErrorGuaranteed,
        syntax::{HasSpan, Span},
    },
    parse::{
        ast::{AstBarePath, AstOptMutability},
        token::{Ident, Lifetime},
    },
};

// === Clauses === //

/// A path with some generic parameters (e.g. `MyStruct<'a, B, C>`, `MyTrait<'a, B, C = D, E: F>`).
#[derive(Debug, Clone)]
pub struct AstNamedSpec {
    pub span: Span,
    pub path: AstBarePath,
    pub params: Option<AstGenericParamList>,
}

/// A list of trait clauses (e.g. `'a + MyImplClause + for<'b> MyOtherClause<'b>`).
#[derive(Debug, Clone)]
pub struct AstTraitClauseList {
    pub span: Span,
    pub clauses: Vec<Result<AstTraitClause, ErrorGuaranteed>>,
}

/// A singular trait clause (e.g. `'a`, `MyImplClause`, `for<'b> MyOtherClause<'b>`).
#[derive(Debug, Clone)]
pub enum AstTraitClause {
    Outlives(Lifetime),
    Trait(AstTraitImplClause),
}

/// A trait clause with an optional HRTB binder.
#[derive(Debug, Clone)]
pub struct AstTraitImplClause {
    pub span: Span,
    pub binder: Option<AstHrtbBinder>,
    pub spec: AstNamedSpec,
}

/// An HRTB binder (e.g. `for<'a, 'b: 'a, T: Spec>`).
#[derive(Debug, Clone)]
pub struct AstHrtbBinder {
    pub span: Span,
    pub params: AstGenericParamList,
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

#[derive(Debug, Copy, Clone)]
pub enum AstGenericDef<'a> {
    Ty(Ident, Option<&'a AstTraitClauseList>),
    Re(Lifetime, Option<&'a AstTraitClauseList>),
}

#[derive(Debug, Copy, Clone)]
pub enum AstGenericPositional<'a> {
    Ty(&'a AstTy),
    Re(&'a Lifetime),
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

    pub fn as_positional(&self) -> Option<AstGenericPositional<'_>> {
        match self {
            AstGenericParamKind::PositionalTy(ty) => Some(AstGenericPositional::Ty(ty)),
            AstGenericParamKind::PositionalRe(re) => Some(AstGenericPositional::Re(re)),
            AstGenericParamKind::InheritTy(..)
            | AstGenericParamKind::InheritRe(..)
            | AstGenericParamKind::TyEquals(..) => None,
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
    Name(AstBarePath, Option<AstGenericParamList>),
    Reference(Option<Lifetime>, AstOptMutability, Box<AstTy>),
    Trait(AstTraitClauseList),
    Paren(Box<AstTy>),
    Tuple(Vec<AstTy>),
    Project(Box<AstTy>, Box<AstNamedSpec>, Ident),
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

    pub fn is_omitted(&self) -> bool {
        matches!(self.kind, AstTyKind::Error(_))
    }
}

#[derive(Debug, Clone)]
pub enum AstReturnTy {
    Omitted,
    Present(AstTy),
}
