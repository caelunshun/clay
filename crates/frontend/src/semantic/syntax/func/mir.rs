use crate::{
    base::{arena::Intern, syntax::Span},
    parse::ast::{AstBinOpKind, AstLit, AstUnOpKind},
    semantic::syntax::{Mutability, Ty},
};
use index_vec::{IndexVec, define_index_type};
use smallvec::SmallVec;
use std::{
    ops::{Bound, RangeBounds},
    slice,
};

// === MirInstructionLoc === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct MirInstructionLoc {
    pub block: MirBlockIdx,
    pub instr: MirInstructionIdx,
}

#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub struct MirInstructionIdx(pub usize);

#[derive(Debug, Copy, Clone)]
pub enum MirInstructionRef<'a> {
    Stmt(&'a MirStmt),
    Terminator(&'a MirTerminator),
}

impl MirInstructionRef<'_> {
    pub fn span(&self) -> Span {
        match self {
            MirInstructionRef::Stmt(stmt) => stmt.span,
            // TODO
            MirInstructionRef::Terminator(_) => Span::DUMMY,
        }
    }
}

// === MirDirection === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirDirection {
    Forward,
    Backward,
}

impl MirDirection {
    pub fn is_forward(self) -> bool {
        matches!(self, Self::Forward)
    }

    pub fn is_backward(self) -> bool {
        matches!(self, Self::Backward)
    }

    pub fn invert(self) -> MirDirection {
        match self {
            MirDirection::Forward => MirDirection::Backward,
            MirDirection::Backward => MirDirection::Forward,
        }
    }
}

// === MirLocal === //

define_index_type! {
    pub struct MirLocalIdx = u32;
}

impl MirLocalIdx {
    pub const RETURN: Self = MirLocalIdx { _raw: 0 };
}

#[derive(Debug, Clone)]
pub struct MirLocal {
    pub ty: Ty,
}

// === MirBody === //

define_index_type! {
    pub struct MirBlockIdx = u32;
}

#[derive(Debug, Clone)]
pub struct MirBody {
    pub locals: IndexVec<MirLocalIdx, MirLocal>,
    pub blocks: IndexVec<MirBlockIdx, MirBlock>,
}

impl MirBody {
    pub fn lookup(&self, loc: MirInstructionLoc) -> MirInstructionRef<'_> {
        self.blocks[loc.block].lookup(loc.instr)
    }
}

#[derive(Debug, Clone, Default)]
pub struct MirBlock {
    pub stmts: Vec<MirStmt>,
    pub terminator: MirTerminator,
    pub predecessors: SmallVec<[MirBlockIdx; 1]>,
}

impl MirBlock {
    pub fn instructions_ranged(
        &self,
        range: impl RangeBounds<MirInstructionIdx>,
    ) -> impl DoubleEndedIterator<Item = MirInstructionIdx> + 'static {
        let start = match range.start_bound() {
            Bound::Included(v) => v.0,
            Bound::Excluded(v) => v.0 + 1,
            Bound::Unbounded => 0,
        };

        let end = match range.end_bound() {
            Bound::Included(v) => v.0 + 1,
            Bound::Excluded(v) => v.0,
            Bound::Unbounded => self.stmts.len() + 1,
        };

        (start..end).map(MirInstructionIdx)
    }

    pub fn instructions(&self) -> impl DoubleEndedIterator<Item = MirInstructionIdx> + 'static {
        self.instructions_ranged(..)
    }

    pub fn terminator_idx(&self) -> MirInstructionIdx {
        MirInstructionIdx(self.stmts.len())
    }

    pub fn lookup(&self, idx: MirInstructionIdx) -> MirInstructionRef<'_> {
        if idx.0 == self.stmts.len() {
            MirInstructionRef::Terminator(&self.terminator)
        } else {
            MirInstructionRef::Stmt(&self.stmts[idx.0])
        }
    }

    pub fn successors(&self) -> &[MirBlockIdx] {
        self.terminator.successors()
    }

    pub fn predecessors(&self) -> &[MirBlockIdx] {
        &self.predecessors
    }

    pub fn prev(&self, direction: MirDirection) -> &[MirBlockIdx] {
        self.next(direction.invert())
    }

    pub fn next(&self, direction: MirDirection) -> &[MirBlockIdx] {
        match direction {
            MirDirection::Forward => self.successors(),
            MirDirection::Backward => self.predecessors(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct MirStmt {
    pub span: Span,
    pub kind: MirStmtKind,
}

#[derive(Debug, Clone)]
pub enum MirStmtKind {
    Assign(Box<(MirPlace, MirAssignRvalue)>),
    Discard(MirOperand),
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

impl MirTerminator {
    pub fn successors(&self) -> &[MirBlockIdx] {
        match self {
            MirTerminator::Goto(target)
            | MirTerminator::Call {
                callee: _,
                args: _,
                destination: _,
                target,
            }
            | MirTerminator::Drop { place: _, target } => slice::from_ref(target),
            MirTerminator::Switch {
                scrutinee: _,
                targets,
            } => targets,
            MirTerminator::Return | MirTerminator::Unreachable | MirTerminator::Placeholder => &[],
        }
    }
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
    Zst,
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
