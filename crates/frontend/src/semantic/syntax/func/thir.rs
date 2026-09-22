use crate::{
    base::{
        ErrorGuaranteed,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::ast::{AstBinOpKind, AstLit, AstUnOpKind},
    semantic::syntax::{
        AdtCtor, AdtCtorFieldIdx, DynSiteIdx, LocalNameIdent, Mutability, PatListFrontAndTail,
        SigTy, ThirLabelledBlock,
    },
};

// === Pattern === //

#[derive(Debug, Clone)]
pub struct ThirLocal {
    pub mutability: Mutability,
    pub name: LocalNameIdent,
    pub ty: SigTy,
}

#[derive(Debug, Clone)]
pub struct ThirPat {
    pub span: Span,
    pub ty: SigTy,
    pub kind: LateInit<ThirPatKind>,
}

#[derive(Debug, Clone)]
pub enum ThirPatKind {
    Hole,
    Binding {
        by_ref: Option<Mutability>,
        local: Obj<ThirLocal>,
        and_bind: Option<Obj<ThirPat>>,
    },
    Deref(Obj<ThirPat>),
    Or(Obj<[Obj<ThirPat>]>),
    Slice(ThirPatListFrontAndTail),
    Tuple(ThirPatListFrontAndTail),
    Adt(Obj<AdtCtor>, Obj<[ThirPatField]>),
    Error(ErrorGuaranteed),
}

#[derive(Debug, Clone)]
pub struct ThirPatField {
    pub idx: AdtCtorFieldIdx,
    pub pat: Obj<ThirPat>,
}

pub type ThirPatListFrontAndTail = PatListFrontAndTail<ThirPat>;

// === Body === //

#[derive(Debug, Clone)]
pub struct ThirExpr {
    pub span: Span,
    pub ty: SigTy,
    pub kind: LateInit<ThirExprKind>,
}

#[derive(Debug, Clone)]
pub enum ThirExprKind {
    CreateZst,
    CreateLiteral(AstLit),
    CreateArray(Obj<[Obj<ThirExpr>]>),
    CreateTuple(Obj<[Obj<ThirExpr>]>),
    PrimitiveBinOp(AstBinOpKind, Obj<ThirExpr>, Obj<ThirExpr>),
    PrimitiveUnOp(AstUnOpKind, Obj<ThirExpr>),
    NoOp(Obj<ThirExpr>),
    Break(ThirLabelledBlock, Option<Obj<ThirExpr>>),
    Continue(ThirLabelledBlock),
    Return(Obj<ThirExpr>),
    Assign(Obj<ThirExpr>, Obj<ThirExpr>),
    Block(Obj<ThirBlock>),
    Loop(Obj<ThirBlock>),
    AddrOf(Mutability, Obj<ThirExpr>),
    Call(Obj<ThirExpr>, Obj<[Obj<ThirExpr>]>),
    Field(Obj<ThirExpr>, u32),
    CreateBracedAdt {
        ctor: Obj<AdtCtor>,
        fields: Obj<[ThirStructField]>,
        rest: Option<Obj<ThirExpr>>,
    },
    Local(Obj<ThirLocal>),
    If {
        cond: Obj<ThirExpr>,
        truthy: Obj<ThirExpr>,
        falsy: Option<Obj<ThirExpr>>,
    },
    DynUse(DynSiteIdx, Obj<ThirExpr>),
    Match(Obj<ThirExpr>, Obj<[ThirMatchArm]>),
    While(Obj<ThirExpr>, Obj<ThirBlock>),
    Let(Obj<ThirPat>, Obj<ThirExpr>),
    Error(ErrorGuaranteed),
}

#[derive(Debug, Clone)]
pub struct ThirMatchArm {
    pub span: Span,
    pub pat: Obj<ThirPat>,
    pub guard: Option<Obj<ThirExpr>>,
    pub body: Obj<ThirExpr>,
}

#[derive(Debug, Clone)]
pub struct ThirStructField {
    pub span: Span,
    pub idx: AdtCtorFieldIdx,
    pub init: Obj<ThirExpr>,
}

#[derive(Debug, Clone)]
pub struct ThirBlock {
    pub span: Span,
    pub ty: SigTy,
    pub stmts: Vec<ThirStmt>,
    pub last_expr: Option<Obj<ThirExpr>>,
}

#[derive(Debug, Copy, Clone)]
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
