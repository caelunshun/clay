use crate::{
    base::{
        ErrorGuaranteed,
        arena::{HasListInterner, Intern, Obj},
        syntax::Span,
    },
    parse::ast::{AstBinOpKind, AstLit, AstUnOpKind},
    semantic::syntax::{AdtCtor, Mutability, SigTy, TyCtxt},
};
use index_vec::{IndexVec, define_index_type};
use smallvec::SmallVec;
use std::ops::{Bound, RangeBounds};

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
    pub ty: SigTy,
}

// === MirBody === //

define_index_type! {
    pub struct MirBlockIdx = u32;
}

#[derive(Debug, Clone, Default)]
pub struct MirBody {
    pub locals: IndexVec<MirLocalIdx, MirLocal>,
    pub blocks: IndexVec<MirBlockIdx, MirBlock>,
}

impl MirBody {
    pub fn lookup(&self, loc: MirInstructionLoc) -> MirInstructionRef<'_> {
        self.blocks[loc.block].lookup(loc.instr)
    }
}

#[derive(Debug, Clone)]
pub struct MirBlock {
    pub stmts: Vec<MirStmt>,
    pub terminator: MirTerminator,
    pub predecessors: SmallVec<[MirBlockIdx; 1]>,
    pub is_unwind: bool,
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

    pub fn successors(&self) -> SmallVec<[MirBlockIdx; 2]> {
        self.terminator.successors()
    }

    pub fn predecessors(&self) -> SmallVec<[MirBlockIdx; 2]> {
        SmallVec::from_iter(self.predecessors.iter().copied())
    }

    pub fn prev(&self, direction: MirDirection) -> SmallVec<[MirBlockIdx; 2]> {
        self.next(direction.invert())
    }

    pub fn next(&self, direction: MirDirection) -> SmallVec<[MirBlockIdx; 2]> {
        match direction {
            MirDirection::Forward => self.successors(),
            MirDirection::Backward => self.predecessors(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct MirStmt {
    pub span: MirStmtSourceInfo,
    pub kind: MirStmtKind,
}

#[derive(Debug, Clone)]
pub enum MirStmtSourceInfo {
    Simple(Span),
    Break,
    Local,
}

#[derive(Debug, Clone)]
pub enum MirStmtKind {
    StorageLive(MirLocalIdx),
    StorageDead(MirLocalIdx),
    Assign(Box<(MirPlace, MirAssignRvalue)>),
    DiscardWithoutDrop(MirAssignRvalue),
}

#[derive(Debug, Clone)]
pub enum MirTerminator {
    Goto(MirBlockIdx),
    SwitchInt {
        discr: MirOperand,
        constants: Box<[u64]>,
        targets: Box<[MirBlockIdx]>,
    },
    Call {
        callee: MirOperand,
        args: Box<[MirOperand]>,
        destination: MirPlace,
        target: MirBlockIdx,
        unwind: MirUnwindBehavior,
    },
    EnsureDropped {
        place: MirPlace,
        target: MirBlockIdx,
        unwind: MirUnwindBehavior,
    },
    CallDrop {
        place: MirPlace,
        target: MirBlockIdx,
        unwind: MirUnwindBehavior,
        drop_flag: Option<MirPlace>,
    },
    Unreachable,
    Return,
    UnwindResume,
    Placeholder,
}

impl MirTerminator {
    pub fn successors(&self) -> SmallVec<[MirBlockIdx; 2]> {
        match *self {
            MirTerminator::Goto(target) => SmallVec::from_iter([target]),
            MirTerminator::Call {
                callee: _,
                args: _,
                destination: _,
                target,
                unwind,
            }
            | MirTerminator::EnsureDropped {
                place: _,
                target,
                unwind,
            } => SmallVec::from_iter([target].into_iter().chain(unwind.block())),
            MirTerminator::CallDrop {
                place: _,
                target,
                unwind,
                drop_flag: _,
            } => SmallVec::from_iter([target].into_iter().chain(unwind.block())),
            MirTerminator::SwitchInt {
                discr: _,
                constants: _,
                ref targets,
            } => SmallVec::from_iter(targets.iter().copied()),
            MirTerminator::UnwindResume
            | MirTerminator::Return
            | MirTerminator::Unreachable
            | MirTerminator::Placeholder => SmallVec::new(),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirUnwindBehavior {
    Continue(MirBlockIdx),
    DoublePanic,
}

impl MirUnwindBehavior {
    pub fn block(self) -> Option<MirBlockIdx> {
        match self {
            MirUnwindBehavior::Continue(idx) => Some(idx),
            MirUnwindBehavior::DoublePanic => None,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct MirPlace {
    pub local: MirLocalIdx,
    pub projections: MirPlaceElemList,
}

impl MirPlace {
    pub fn new(
        tcx: &TyCtxt,
        local: MirLocalIdx,
        projections: impl IntoIterator<Item = MirPlaceElem>,
    ) -> Self {
        Self {
            local,
            projections: tcx.intern_list(&projections.into_iter().collect::<Vec<_>>()),
        }
    }

    pub fn extend(self, tcx: &TyCtxt, proj: impl IntoIterator<Item = MirPlaceElem>) -> Self {
        let s = &tcx.session;

        Self {
            local: self.local,
            projections: tcx.intern_list(
                &self
                    .projections
                    .r(s)
                    .iter()
                    .copied()
                    .chain(proj)
                    .collect::<Vec<_>>(),
            ),
        }
    }
}

pub type MirPlaceElemList = Intern<[MirPlaceElem]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirPlaceElem {
    DerefPtr,
    Field(u32),
}

#[derive(Debug, Clone)]
pub enum MirAssignRvalue {
    Tuple(Box<[MirOperand]>),
    Adt(Obj<AdtCtor>, Box<[MirOperand]>),
    Use(MirOperand),
    MoveOutRef {
        can_move_from: Vec<MirPlace>,
        ref_place: MirPlace,
    },
    Ref(Mutability, MirPlace),
    Zst(SigTy),
    Literal(SigTy, AstLit),
    BinaryOp(AstBinOpKind, Box<(MirOperand, MirOperand)>),
    UnaryOp(AstUnOpKind, MirOperand),
    Discriminant(MirPlace),
    Error(ErrorGuaranteed),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirOperandMode {
    Copy,
    Move,
}

impl MirOperandMode {
    pub fn is_copy(self) -> bool {
        self == Self::Copy
    }

    pub fn to_operand(self, place: MirPlace) -> MirOperand {
        match self {
            MirOperandMode::Copy => MirOperand::Copy(place),
            MirOperandMode::Move => MirOperand::Move(place),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirOperand {
    Copy(MirPlace),
    Move(MirPlace),
}

impl MirOperand {
    pub fn place(self) -> MirPlace {
        let (MirOperand::Copy(place) | MirOperand::Move(place)) = self;

        place
    }
}
