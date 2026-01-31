use crate::{
    base::{
        ErrorGuaranteed, Session,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::{
        ast::{AstAssignOpKind, AstBinOpSpanned, AstLit, AstRangeLimits, AstUnOpKind},
        token::Ident,
    },
    semantic::syntax::{
        AdtCtorFieldIdx, AdtCtorInstance, GenericBinder, ImplItem, Item, Mutability,
        SpannedTraitInstance, SpannedTy, SpannedTyOrRe, SpannedTyOrReList, Ty,
    },
};
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign};

// === FuncItem === //

#[derive(Debug, Clone)]
pub struct FuncItem {
    pub item: Obj<Item>,
    pub def: LateInit<Obj<FnDef>>,
}

#[derive(Debug, Clone)]
pub struct FnDef {
    pub span: Span,
    pub owner: FuncDefOwner,
    pub name: Ident,
    pub generics: Obj<GenericBinder>,
    pub self_param: LateInit<Option<SpannedTy>>,
    pub args: LateInit<Obj<[FuncArg]>>,
    pub ret_ty: LateInit<SpannedTy>,
    pub body: LateInit<Option<Obj<Block>>>,
}

#[derive(Debug, Copy, Clone)]
pub enum FuncDefOwner {
    Func(Obj<FuncItem>),
    Method(Obj<ImplItem>, u32),
}

#[derive(Debug, Clone)]
pub struct FuncArg {
    pub span: Span,
    pub pat: Obj<Pat>,
    pub ty: SpannedTy,
}

#[derive(Debug, Clone)]
pub struct FuncLocal {
    pub mutability: Mutability,
    pub name: Ident,
}

// === Pattern === //

#[derive(Debug, Clone)]
pub struct Pat {
    pub span: Span,
    pub kind: PatKind,
}

#[derive(Debug, Clone)]
pub enum PatKind {
    /// Ignore the destructure target.
    Hole,

    /// Define a new local. Only available in defining patterns.
    NewName(Obj<FuncLocal>, Option<Obj<Pat>>),

    /// Match an array or slice of patterns.
    Slice(PatListFrontAndTail),

    /// Match a tuple of patterns.
    Tuple(PatListFrontAndTail),

    /// Match a literal.
    Lit(Obj<Expr>),

    /// Match a variety of options.
    Or(Obj<[Obj<Pat>]>),

    /// Match the dereference of something.
    Ref(Mutability, Obj<Pat>),

    /// Match a unit struct or enum variant.
    AdtUnit(AdtCtorInstance),

    /// Match a tuple struct or enum variant.
    AdtTuple(AdtCtorInstance, PatListFrontAndTail),

    /// Match a named struct or enum variant.
    AdtNamed(AdtCtorInstance, Obj<[PatNamedField]>),

    /// Bind to a target place expression. Only available in destructuring patterns.
    PlaceExpr(Obj<Expr>),

    /// Matches a range of scalar values.
    Range(RangeExpr),

    /// Failed to lower the pattern.
    Error(ErrorGuaranteed),
}

#[derive(Debug, Copy, Clone)]
pub struct PatNamedField {
    pub idx: AdtCtorFieldIdx,
    pub pat: Obj<Pat>,
}

#[derive(Debug, Copy, Clone)]
pub struct PatListFrontAndTail {
    pub front: Obj<[Obj<Pat>]>,
    pub tail: Option<Obj<[Obj<Pat>]>>,
}

impl PatListFrontAndTail {
    pub fn len(self, s: &Session) -> PatListFrontAndTailLen {
        if let Some(tail) = self.tail {
            PatListFrontAndTailLen::AtLeast(self.front.r(s).len() as u32 + tail.r(s).len() as u32)
        } else {
            PatListFrontAndTailLen::Exactly(self.front.r(s).len() as u32)
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum PatListFrontAndTailLen {
    Exactly(u32),
    AtLeast(u32),
}

// === Block === //

#[derive(Debug, Clone)]
pub struct Block {
    pub span: Span,
    pub stmts: Vec<Stmt>,
    pub last_expr: Option<Obj<Expr>>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum Stmt {
    Expr(Obj<Expr>),
    Let(Obj<LetStmt>),
}

#[derive(Debug, Clone)]
pub struct LetStmt {
    pub span: Span,
    pub pat: Obj<Pat>,
    pub ascription: Option<SpannedTy>,
    pub init: Option<Obj<Expr>>,
    pub else_clause: Option<Obj<Block>>,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub span: Span,
    pub kind: LateInit<ExprKind>,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Array(Obj<[Obj<Expr>]>),
    Call(Obj<Expr>, Obj<[Obj<Expr>]>),
    Method {
        callee: Obj<Expr>,
        generics: Option<SpannedTyOrRe>,
        args: Obj<[Obj<Expr>]>,
    },
    Tuple(Obj<[Obj<Expr>]>),
    Binary(AstBinOpSpanned, Obj<Expr>, Obj<Expr>),
    Unary(AstUnOpKind, Obj<Expr>),
    Literal(AstLit),
    TupleOrUnitCtor(AdtCtorInstance),
    FnItemLit(Obj<FuncItem>, SpannedTyOrReList),
    TypeRelative {
        self_ty: SpannedTy,
        as_trait: Option<SpannedTraitInstance>,
        assoc_name: Ident,
        assoc_args: Option<SpannedTyOrReList>,
    },
    Cast(Obj<Expr>, SpannedTy),
    If {
        cond: Obj<Expr>,
        truthy: Obj<Expr>,
        falsy: Option<Obj<Expr>>,
    },
    While(Obj<Expr>, Obj<Block>),
    Let(Obj<Pat>, Obj<Expr>),
    ForLoop {
        pat: Obj<Pat>,
        iter: Obj<Expr>,
        body: Obj<Block>,
    },
    Loop(Obj<Block>),
    Match(Obj<Expr>, Obj<[Obj<MatchArm>]>),
    Block(Obj<Block>),
    Assign(Obj<Pat>, Obj<Expr>),
    AssignOp(AstAssignOpKind, Obj<Pat>, Obj<Expr>),
    Field(Obj<Expr>, Ident),
    GenericMethodCall {
        target: Obj<Expr>,
        method: Ident,
        generics: SpannedTyOrReList,
        args: Obj<[Obj<Expr>]>,
    },
    Index(Obj<Expr>, Obj<Expr>),
    Range(RangeExpr),
    LocalSelf,
    Local(Obj<FuncLocal>),
    AddrOf(Mutability, Obj<Expr>),
    Break {
        label: Option<Obj<Expr>>,
        expr: Option<Obj<Expr>>,
    },
    Continue {
        label: Option<Obj<Expr>>,
    },
    Return(Option<Obj<Expr>>),
    Struct(StructExpr),
    Error(ErrorGuaranteed),
}

#[derive(Debug, Copy, Clone)]
pub struct RangeExpr {
    pub low: Option<Obj<Expr>>,
    pub high: Option<Obj<Expr>>,
    pub limits: AstRangeLimits,
}

#[derive(Debug, Copy, Clone)]
pub struct StructExpr {
    pub ctor: AdtCtorInstance,
    pub fields: Obj<[StructNamedField]>,
    pub rest: Option<Obj<Expr>>,
}

#[derive(Debug, Copy, Clone)]
pub struct StructNamedField {
    pub idx: AdtCtorFieldIdx,
    pub init: Obj<Expr>,
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub span: Span,
    pub pat: Obj<Pat>,
    pub guard: Option<Obj<Expr>>,
    pub body: Obj<Expr>,
}

// === Divergence === //

#[derive(Debug, Copy, Clone)]
pub struct TyAndDivergence {
    pub ty: Ty,
    pub divergence: Divergence,
}

impl TyAndDivergence {
    pub const fn new(ty: Ty, divergence: Divergence) -> Self {
        Self { ty, divergence }
    }

    pub fn and_do(self, divergence: &mut Divergence) -> Ty {
        *divergence &= self.divergence;
        self.ty
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum Divergence {
    MustDiverge,
    MayDiverge,
}

impl BitOr for Divergence {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Divergence::MustDiverge, Divergence::MustDiverge) => Divergence::MustDiverge,
            _ => Divergence::MayDiverge,
        }
    }
}

impl BitOrAssign for Divergence {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl BitAnd for Divergence {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Divergence::MayDiverge, Divergence::MayDiverge) => Divergence::MayDiverge,
            _ => Divergence::MustDiverge,
        }
    }
}

impl BitAndAssign for Divergence {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl Divergence {
    pub fn must_diverge(self) -> bool {
        matches!(self, Self::MustDiverge)
    }
}
