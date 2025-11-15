use crate::{
    base::{arena::Obj, syntax::Span},
    parse::{
        ast::{AstBinOpKind, AstLit, AstRangeLimits, AstUnOpKind},
        token::Ident,
    },
    semantic::syntax::{
        AdtDef, GenericBinder, Item, Mutability, SpannedTraitParamList, SpannedTy, SpannedTyOrRe,
        TraitMethod,
    },
};

// === FuncItem === //

#[derive(Debug, Clone)]
pub struct FuncItem {
    pub item: Obj<Item>,
    pub def: Obj<FuncDef>,
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub span: Span,
    pub name: Ident,
    pub generics: Obj<GenericBinder>,
    pub self_ty: Option<SpannedTy>,
    pub args: Obj<[FuncArg]>,
    pub ret_ty: Option<SpannedTy>,
    pub body: Obj<Block>,
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
    pub kind: Obj<PatKind>,
}

#[derive(Debug, Clone)]
pub enum PatKind {
    Name(Obj<FuncLocal>),
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
    pub lhs: Obj<Pat>,
    pub ascription: Option<SpannedTy>,
    pub rhs: Obj<Expr>,
    pub else_clause: Option<Obj<Block>>,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
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
    FuncLit(Obj<FuncDef>, SpannedTyOrRe),
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
        truthy: Obj<Block>,
        falsy: Obj<Expr>,
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
    Assign(Obj<Pat>, Obj<Expr>),
    AssignOp(AstBinOpKind, Obj<Expr>, Obj<Expr>),
    Field(Obj<Expr>, Ident),
    Index(Obj<Expr>, Obj<Expr>),
    Range(Option<Obj<Expr>>, Option<Obj<Expr>>, AstRangeLimits),
    Local(Obj<FuncLocal>),
    AddrOf(Mutability, Obj<Expr>),
    Break {
        label: Option<Obj<Expr>>,
        expr: Obj<Expr>,
    },
    Continue {
        label: Option<Obj<Expr>>,
    },
    Return(Obj<Expr>),
    Struct(Obj<AdtDef>), // TODO
}
