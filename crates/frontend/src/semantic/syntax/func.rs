use crate::{
    base::{
        ErrorGuaranteed,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::{
        ast::{AstAssignOpKind, AstBinOpKind, AstLit, AstRangeLimits, AstUnOpKind},
        token::Ident,
    },
    semantic::syntax::{
        AdtDef, AdtKindStruct, EnumVariantItem, GenericBinder, ImplDef, Item, Mutability,
        SpannedTraitInstance, SpannedTy, SpannedTyOrRe, SpannedTyOrReList,
    },
};

// === FuncItem === //

#[derive(Debug, Clone)]
pub struct FnItem {
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
    pub ret_ty: LateInit<Option<SpannedTy>>,
    pub body: LateInit<Option<Obj<Block>>>,
}

#[derive(Debug, Copy, Clone)]
pub enum FuncDefOwner {
    Func(Obj<FnItem>),
    Method(Obj<ImplDef>, u32),
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

    /// Ignore the remainder of a structure.
    Rest,

    /// Define a new local. Only available in defining patterns.
    NewName(Obj<FuncLocal>),

    /// Match an array or slice of patterns.
    Slice(Obj<[Obj<Pat>]>),

    /// Match a tuple of patterns.
    Tuple(Obj<[Obj<Pat>]>),

    /// Match a literal.
    Lit(Obj<Expr>),

    /// Match a variety of options.
    Or(Obj<[Obj<Pat>]>),

    /// Bind to a target place expression. Only available in destructuring patterns.
    PlaceExpr(Obj<Expr>),

    /// Failed to lower the pattern.
    Error(ErrorGuaranteed),
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
    Binary(AstBinOpKind, Obj<Expr>, Obj<Expr>),
    Unary(AstUnOpKind, Obj<Expr>),
    Literal(AstLit),
    StructCtorLit(Obj<AdtKindStruct>, SpannedTyOrReList),
    EnumCtorLit(Obj<EnumVariantItem>, SpannedTyOrReList),
    FuncLit(Obj<FnItem>, SpannedTyOrReList),
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
    ForLoop {
        pat: Obj<Pat>,
        iter: Obj<Expr>,
        body: Obj<Block>,
    },
    Loop(Obj<Block>),
    Match(Obj<Expr>, Obj<[Obj<MatchArm>]>),
    // TODO
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
    Range(Option<Obj<Expr>>, Option<Obj<Expr>>, AstRangeLimits),
    SelfLocal,
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
    Struct(Obj<AdtDef>), // TODO
    Error(ErrorGuaranteed),
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub span: Span,
    pub pat: Obj<Pat>,
    pub guard: Option<Obj<Expr>>,
    pub body: Obj<Expr>,
}
