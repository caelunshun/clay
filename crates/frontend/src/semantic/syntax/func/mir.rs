use crate::{
    base::arena::Intern,
    parse::ast::{AstBinOpKind, AstLit, AstUnOpKind},
    semantic::syntax::Mutability,
};
use index_vec::{IndexVec, define_index_type};

define_index_type! {
    pub struct MirLocalIdx = u32;
}

impl MirLocalIdx {
    pub const RETURN: Self = MirLocalIdx { _raw: 0 };
}

define_index_type! {
    pub struct MirBlockIdx = u32;
}

#[derive(Debug, Clone)]
pub struct MirBody {
    pub locals: IndexVec<MirLocalIdx, MirLocal>,
    pub blocks: IndexVec<MirBlockIdx, MirBlock>,
}

#[derive(Debug, Clone)]
pub struct MirLocal {}

#[derive(Debug, Clone, Default)]
pub struct MirBlock {
    pub stmts: Vec<MirStmt>,
    pub terminator: MirTerminator,
}

#[derive(Debug, Clone)]
pub struct MirStmt {
    pub kind: MirStmtKind,
}

#[derive(Debug, Clone)]
pub enum MirStmtKind {
    Assign(Box<(MirPlace, MirAssignRvalue)>),
}

#[derive(Debug, Clone, Default)]
pub enum MirTerminator {
    Goto(MirBlockIdx),
    Call {
        callee: MirOperand,
        args: Box<[MirOperand]>,
        destination: MirPlace,
        target: MirBlockIdx,
    },
    Drop {
        place: MirPlace,
        target: MirBlockIdx,
    },
    Switch {
        scrutinee: MirPlace,
        targets: Box<[MirBlockIdx]>,
    },
    Return,
    Unreachable,
    #[default]
    Placeholder,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct MirPlace {
    pub local: MirLocalIdx,
    pub projections: MirPlaceElemList,
}

pub type MirPlaceElemList = Intern<[MirPlaceElem]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirPlaceElem {
    DerefPtr,
}

#[derive(Debug, Clone)]
pub enum MirAssignRvalue {
    Tuple(Box<[MirOperand]>),
    Use(MirOperand),
    Ref(Mutability, MirPlace),
    Literal(AstLit),
    BinaryOp(AstBinOpKind, Box<(MirOperand, MirOperand)>),
    UnaryOp(AstUnOpKind, MirOperand),
    Discriminant(MirPlace),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirOperand {
    Copy(MirPlace),
    Move(MirPlace),
}
