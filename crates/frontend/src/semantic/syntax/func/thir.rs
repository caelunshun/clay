use crate::{
    base::{ErrorGuaranteed, arena::Obj, syntax::Span},
    parse::ast::{AstBinOpKind, AstLit, AstUnOpKind},
    semantic::syntax::{FnLocal, Mutability, Ty},
};

// === Pattern === //

#[derive(Debug, Clone)]
pub struct ThirPat {
    pub span: Span,
    pub ty: Ty,
    pub kind: ThirPatKind,
}

#[derive(Debug, Clone)]
pub enum ThirPatKind {
    Wild,
    Binding(Obj<FnLocal>, Option<Obj<ThirPat>>),
    Deref(Obj<ThirPat>),
    Or(Obj<[Obj<ThirPat>]>),
    Error(ErrorGuaranteed),
}

// === Body === //

#[derive(Debug, Clone)]
pub struct ThirExpr {
    pub span: Span,
    pub ty: Ty,
    pub kind: ThirExprKind,
}

#[derive(Debug, Clone)]
pub enum ThirExprKind {
    CreatePathZst,
    CreateLiteral(AstLit),
    CreateTuple(Obj<[Obj<ThirExpr>]>),
    PrimitiveBinOp(AstBinOpKind, Obj<ThirExpr>, Obj<ThirExpr>),
    PrimitiveUnOp(AstUnOpKind, Obj<ThirExpr>),
    Return(Obj<ThirExpr>),
    Block(Obj<ThirBlock>),
    Loop(Obj<ThirBlock>),
    AddrOf(Mutability, Obj<ThirExpr>),
    Call(Obj<ThirExpr>, Obj<[Obj<ThirExpr>]>),
    Local(Obj<FnLocal>),
    Error(ErrorGuaranteed),
}

#[derive(Debug, Clone)]
pub struct ThirBlock {
    pub span: Span,
    pub ty: Ty,
    pub stmts: Vec<ThirStmt>,
    pub last_expr: Option<Obj<ThirExpr>>,
}

#[derive(Debug, Clone)]
pub enum ThirStmt {
    Expr(Obj<ThirExpr>),
    Let(Obj<ThirLetStmt>),
}

#[derive(Debug, Clone)]
pub struct ThirLetStmt {
    pub span: Span,
    pub pat: Obj<ThirPat>,
    pub init: Option<Obj<ThirExpr>>,
    pub else_clause: Option<Obj<ThirBlock>>,
}
