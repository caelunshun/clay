use crate::base::{
    arena::Obj,
    syntax::{Span, Symbol},
};

// === Module === //

#[derive(Debug)]
pub struct HirModule {
    pub children: Vec<Obj<HirBody>>,
}

// === Body === //

#[derive(Debug)]
pub struct HirBody {
    pub span: Span,
    pub name: Symbol,
    pub parent: Option<Obj<HirBody>>,
    pub generics: Vec<()>,
    pub args: Vec<()>,
    pub ret_ty: Obj<HirTy>,
}

#[derive(Debug)]
pub struct HirBodyArgument {}

#[derive(Debug)]
pub enum HirName {
    Local(),
}

#[derive(Debug)]
pub struct HirTy {
    pub span: Span,
    pub kind: HirTyKind,
}

#[derive(Debug)]
pub enum HirTyKind {}
