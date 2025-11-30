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
        AdtDef, GenericBinder, ImplDef, Item, Mutability, SpannedTraitParamList, SpannedTy,
        SpannedTyOrRe, TraitMethod,
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
    Wild,
    Name(Obj<FuncLocal>),
    Or(Obj<[Obj<Pat>]>),
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
    FuncLit(Obj<FnDef>, SpannedTyOrRe),
    TraitMethodLit {
        method: Obj<TraitMethod>,
        trait_params: Option<SpannedTraitParamList>,
        method_params: SpannedTyOrRe,
    },
    TypeMethodLit {
        ty: SpannedTy,
        name: Ident,
        params: SpannedTyOrRe,
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
    // TODO
    Block(Obj<Block>),
    Assign(Obj<Expr>, Obj<Expr>),
    Destructure(Obj<Pat>, Obj<Expr>),
    AssignOp(AstAssignOpKind, Obj<Expr>, Obj<Expr>),
    Field(Obj<Expr>, Ident),
    Index(Obj<Expr>, Obj<Expr>),
    Range(Option<Obj<Expr>>, Option<Obj<Expr>>, AstRangeLimits),
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
