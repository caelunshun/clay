use crate::{
    base::{
        ErrorGuaranteed, Session,
        arena::{LateInit, Obj},
        syntax::{HasSpan, Span, Symbol},
    },
    parse::{
        ast::{
            AstAssignOpKind, AstBinOpSpanned, AstLit, AstOptMutability, AstRangeLimits, AstUnOpKind,
        },
        token::Ident,
    },
    semantic::syntax::{
        EnumVariantItem, FnItem, HirLabelledBlock, Mutability, SigTraitSpec, SigTy, SigTyOrReList,
    },
};
use std::fmt;

// === Pattern === //

#[derive(Debug, Clone)]
pub struct HirLocal {
    pub mutability: Mutability,
    pub name: LocalNameIdent,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum LocalNameIdent {
    User(Ident),
    SelfName(Span),
}

impl fmt::Display for LocalNameIdent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_symbol().fmt(f)
    }
}

impl LocalNameIdent {
    pub fn with_span(self, span: Span) -> Self {
        match self {
            LocalNameIdent::User(ident) => LocalNameIdent::User(ident.with_span(span)),
            LocalNameIdent::SelfName(_span) => LocalNameIdent::SelfName(span),
        }
    }

    pub fn as_symbol(self) -> LocalNameSymbol {
        match self {
            LocalNameIdent::User(ident) => LocalNameSymbol::User(ident.text),
            LocalNameIdent::SelfName(_span) => LocalNameSymbol::SelfName,
        }
    }
}

impl HasSpan for LocalNameIdent {
    fn span(&self) -> Span {
        match *self {
            LocalNameIdent::User(ident) => ident.span,
            LocalNameIdent::SelfName(span) => span,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum LocalNameSymbol {
    User(Symbol),
    SelfName,
}

impl fmt::Display for LocalNameSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LocalNameSymbol::User(symbol) => symbol.fmt(f),
            LocalNameSymbol::SelfName => f.write_str("self"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct HirPat {
    pub span: Span,
    pub kind: HirPatKind,
}

#[derive(Debug, Clone)]
pub enum HirPatKind {
    /// Ignore the destructure target.
    Hole,

    /// Define a new local. Only available in defining patterns.
    Binding(AstOptMutability, Obj<HirLocal>, Option<Obj<HirPat>>),

    /// Match an array or slice of patterns.
    Slice(HirPatListFrontAndTail),

    /// Match a tuple of patterns.
    Tuple(HirPatListFrontAndTail),

    /// Match a literal.
    Lit(Obj<HirExpr>),

    /// Match a variety of options.
    Or(Obj<[Obj<HirPat>]>),

    /// Match the dereference of something.
    Deref(Mutability, Obj<HirPat>),

    /// Match a unit struct or enum variant.
    AdtUnit(AdtCtorUnresolved),

    /// Match a tuple struct or enum variant.
    AdtTuple(AdtCtorUnresolved, HirPatListFrontAndTail),

    /// Match a named struct or enum variant.
    AdtNamed(AdtCtorUnresolved, Obj<[HirPatNamedField]>),

    /// Bind to a target place expression. Only available in destructuring patterns.
    PlaceExpr(Obj<HirExpr>),

    /// Matches a range of scalar values.
    Range(HirRangeExpr),

    /// Failed to lower the pattern.
    Error(ErrorGuaranteed),
}

#[derive(Debug, Copy, Clone)]
pub enum AdtCtorUnresolved {
    ResolvedTy(SigTy),
    ResolvedEnumVariant(Obj<EnumVariantItem>, SigTyOrReList),
    UnresolvedEnumVariant(SigTy, Ident),
}

#[derive(Debug, Copy, Clone)]
pub struct HirPatNamedField {
    pub name: Ident,
    pub pat: Obj<HirPat>,
}

#[derive(Debug, Copy, Clone)]
pub struct HirPatListFrontAndTail {
    pub front: Obj<[Obj<HirPat>]>,
    pub tail: Option<Obj<[Obj<HirPat>]>>,
}

impl HirPatListFrontAndTail {
    pub fn len(self, s: &Session) -> HirPatListFrontAndTailLen {
        if let Some(tail) = self.tail {
            HirPatListFrontAndTailLen::AtLeast(
                self.front.r(s).len() as u32 + tail.r(s).len() as u32,
            )
        } else {
            HirPatListFrontAndTailLen::Exactly(self.front.r(s).len() as u32)
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum HirPatListFrontAndTailLen {
    Exactly(u32),
    AtLeast(u32),
}

// === Body === //

#[derive(Debug, Clone)]
pub struct HirBlock {
    pub span: Span,
    pub stmts: Vec<HirStmt>,
    pub last_expr: Option<Obj<HirExpr>>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum HirStmt {
    Expr(Obj<HirExpr>),
    Let(Obj<HirLetStmt>),
}

#[derive(Debug, Clone)]
pub struct HirLetStmt {
    pub span: Span,
    pub pat: Obj<HirPat>,
    pub ascription: Option<SigTy>,
    pub init: Option<Obj<HirExpr>>,
    pub else_clause: Option<Obj<HirBlock>>,
}

#[derive(Debug, Clone)]
pub struct HirExpr {
    pub span: Span,
    pub kind: LateInit<HirExprKind>,
}

#[derive(Debug, Clone)]
pub enum HirExprKind {
    Array(Obj<[Obj<HirExpr>]>),
    Call(Obj<HirExpr>, Obj<[Obj<HirExpr>]>),
    Tuple(Obj<[Obj<HirExpr>]>),
    Binary(AstBinOpSpanned, Obj<HirExpr>, Obj<HirExpr>),
    Unary(AstUnOpKind, Obj<HirExpr>),
    Literal(AstLit),
    AdtCtorTy(SigTy),
    AdtCtorEnumVariant(Obj<EnumVariantItem>, SigTyOrReList),
    FnItemLit(Obj<FnItem>, Option<SigTyOrReList>),
    TypeRelative {
        self_ty: SigTy,
        as_trait: Option<SigTraitSpec>,
        assoc_name: Ident,
        assoc_args: Option<SigTyOrReList>,
    },
    Cast(Obj<HirExpr>, SigTy),
    If {
        cond: Obj<HirExpr>,
        truthy: Obj<HirExpr>,
        falsy: Option<Obj<HirExpr>>,
    },
    While(Obj<HirExpr>, Obj<HirBlock>),
    Let(Obj<HirPat>, Obj<HirExpr>),
    ForLoop {
        pat: Obj<HirPat>,
        iter: Obj<HirExpr>,
        body: Obj<HirBlock>,
    },
    Loop(Obj<HirBlock>),
    Match(Obj<HirExpr>, Obj<[Obj<HirMatchArm>]>),
    Block(Obj<HirBlock>),
    Assign(Obj<HirPat>, Obj<HirExpr>),
    AssignOp(AstAssignOpKind, Obj<HirPat>, Obj<HirExpr>),
    Field(Obj<HirExpr>, Ident),
    MethodCall {
        receiver: Obj<HirExpr>,
        name: Ident,
        generics: Option<SigTyOrReList>,
        args: Obj<[Obj<HirExpr>]>,
    },
    Index(Obj<HirExpr>, Obj<HirExpr>),
    Range(HirRangeExpr),
    Local(Obj<HirLocal>),
    AddrOf(Mutability, Obj<HirExpr>),
    Break {
        label: HirLabelledBlock,
        value: Option<Obj<HirExpr>>,
    },
    Continue(HirLabelledBlock),
    Return(Obj<HirExpr>),
    Struct(HirStructExpr),
    Error(ErrorGuaranteed),
}

#[derive(Debug, Copy, Clone)]
pub struct HirRangeExpr {
    pub low: Option<Obj<HirExpr>>,
    pub high: Option<Obj<HirExpr>>,
    pub limits: AstRangeLimits,
}

#[derive(Debug, Copy, Clone)]
pub struct HirStructExpr {
    pub ctor_span: Span,
    pub ctor: AdtCtorUnresolved,
    pub fields: Obj<[HirStructNamedField]>,
    pub rest: Option<Obj<HirExpr>>,
}

#[derive(Debug, Copy, Clone)]
pub struct HirStructNamedField {
    pub name: Ident,
    pub init: Obj<HirExpr>,
}

#[derive(Debug, Clone)]
pub struct HirMatchArm {
    pub span: Span,
    pub pat: Obj<HirPat>,
    pub guard: Option<Obj<HirExpr>>,
    pub body: Obj<HirExpr>,
}
