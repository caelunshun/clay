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
        AdtCtorUnresolved, EnumVariantItem, FnItem, Mutability, SpannedTraitSpec, SpannedTy,
        SpannedTyOrReList,
    },
    symbol,
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
    pub ascription: Option<SpannedTy>,
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
    AdtCtorTy(SpannedTy),
    AdtCtorEnumVariant(Obj<EnumVariantItem>, SpannedTyOrReList),
    FnItemLit(Obj<FnItem>, Option<SpannedTyOrReList>),
    TypeRelative {
        self_ty: SpannedTy,
        as_trait: Option<SpannedTraitSpec>,
        assoc_name: Ident,
        assoc_args: Option<SpannedTyOrReList>,
    },
    Cast(Obj<HirExpr>, SpannedTy),
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
        generics: Option<SpannedTyOrReList>,
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

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct HirLabelledBlock {
    pub target: Obj<HirExpr>,
    pub kind: HirLabelTargetKind,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum HirLabelTargetKind {
    Loop,
    While,
    For,
    Block,
}

impl HirLabelTargetKind {
    pub fn implicit_innermost(self) -> bool {
        match self {
            HirLabelTargetKind::Loop | HirLabelTargetKind::While | HirLabelTargetKind::For => true,
            HirLabelTargetKind::Block => false,
        }
    }

    pub fn can_break_with_value(self) -> bool {
        match self {
            HirLabelTargetKind::Loop | HirLabelTargetKind::Block => true,
            HirLabelTargetKind::While | HirLabelTargetKind::For => false,
        }
    }

    pub fn can_continue(self) -> bool {
        match self {
            HirLabelTargetKind::Loop | HirLabelTargetKind::While | HirLabelTargetKind::For => true,
            HirLabelTargetKind::Block => false,
        }
    }

    pub fn what(self) -> Symbol {
        match self {
            HirLabelTargetKind::Loop => symbol!("`loop`"),
            HirLabelTargetKind::While => symbol!("`while` loop"),
            HirLabelTargetKind::For => symbol!("`for` loop"),
            HirLabelTargetKind::Block => symbol!("named block"),
        }
    }

    pub fn a_what(self) -> Symbol {
        match self {
            HirLabelTargetKind::Loop => symbol!("a `loop`"),
            HirLabelTargetKind::While => symbol!("a `while` loop"),
            HirLabelTargetKind::For => symbol!("a `for` loop"),
            HirLabelTargetKind::Block => symbol!("a named block"),
        }
    }
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
