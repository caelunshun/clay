use crate::{
    base::{
        ErrorGuaranteed,
        arena::{HasListInterner as _, Intern, Obj},
        syntax::Span,
    },
    parse::ast::{AstBinOpKind, AstLit, AstUnOpKind},
    semantic::syntax::{AdtCtor, DynSiteIdx, Mutability, ResolvedFieldIdx, SigTy, TyCtxt},
};
use index_vec::{IndexVec, define_index_type};
use slotmap::{SlotMap, new_key_type};
use smallvec::SmallVec;
use std::mem;

// === MirBody === //

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

#[derive(Debug, Clone)]
pub struct MirBody {
    pub locals: IndexVec<MirLocalIdx, MirLocal>,
    pub entry: MirBlockIdx,
    pub cfg: MirBodyCfg,
}

impl Default for MirBody {
    fn default() -> Self {
        let mut body = Self {
            locals: IndexVec::default(),
            entry: MirBlockIdx::default(),
            cfg: MirBodyCfg::default(),
        };

        body.entry = body.cfg.create_block();

        body
    }
}

// === MirBodyCfg === //

new_key_type! {
    pub struct MirBlockIdx;

    pub struct MirStmtIdx;
}

#[derive(Debug, Copy, Clone)]
pub enum MirLocationAfter {
    BlockStart(MirBlockIdx),
    Stmt(MirStmtIdx),
}

#[derive(Debug, Copy, Clone)]
pub enum MirLocationBefore {
    Terminator(MirBlockIdx),
    Stmt(MirStmtIdx),
}

#[derive(Debug, Clone, Default)]
pub struct MirBodyCfg {
    blocks: SlotMap<MirBlockIdx, MirBlockNode>,
    stmts: SlotMap<MirStmtIdx, MirStmtNode>,
}

#[derive(Debug, Clone)]
pub struct MirBlockNode {
    predecessors: SmallVec<[MirBlockIdx; 2]>,
    successors: SmallVec<[MirBlockIdx; 2]>,
    first_stmt: Option<MirStmtIdx>,
    last_stmt: Option<MirStmtIdx>,
    terminator: Option<MirTerminator>,
}

#[derive(Debug, Clone)]
pub struct MirStmtNode {
    block: Option<MirBlockIdx>,
    prev_stmt: Option<MirStmtIdx>,
    next_stmt: Option<MirStmtIdx>,
    stmt: Option<MirStmt>,
}

impl MirBodyCfg {
    pub fn create_block(&mut self) -> MirBlockIdx {
        self.blocks.insert(MirBlockNode {
            predecessors: SmallVec::new(),
            successors: SmallVec::new(),
            first_stmt: None,
            last_stmt: None,
            terminator: None,
        })
    }

    pub fn create_block_with_terminator(&mut self, terminator: MirTerminator) -> MirBlockIdx {
        let idx = self.create_block();
        self.init_terminator(idx, terminator);
        idx
    }

    pub fn create_stmt(&mut self) -> MirStmtIdx {
        self.stmts.insert(MirStmtNode {
            block: None,
            prev_stmt: None,
            next_stmt: None,
            stmt: None,
        })
    }

    pub fn push_stmt(&mut self, block: MirBlockIdx, stmt: MirStmt) -> MirStmtIdx {
        let idx = self.create_stmt();
        self.move_stmt_before(idx, MirLocationBefore::Terminator(block));
        self.init_stmt(idx, stmt);
        idx
    }

    pub fn move_stmt_after(&mut self, idx: MirStmtIdx, after: MirLocationAfter) {
        self.unlink_mir_stmt(idx);

        match after {
            MirLocationAfter::BlockStart(block) => {
                self.stmts[idx].block = Some(block);

                let old_first_stmt = self.blocks[block].first_stmt.replace(idx);

                if old_first_stmt.is_some() {
                    self.stmts[idx].next_stmt = old_first_stmt;
                } else {
                    self.blocks[block].last_stmt = Some(idx);
                }
            }
            MirLocationAfter::Stmt(after) => {
                let block = self.stmts[after]
                    .block
                    .expect("cannot relate statements outside of a basic block");

                self.stmts[idx].block = Some(block);

                let old_next_stmt = self.stmts[after].next_stmt.replace(idx);

                if old_next_stmt.is_some() {
                    self.stmts[idx].next_stmt = old_next_stmt;
                } else {
                    self.blocks[block].last_stmt = Some(idx);
                }
            }
        }
    }

    pub fn move_stmt_before(&mut self, idx: MirStmtIdx, before: MirLocationBefore) {
        self.unlink_mir_stmt(idx);

        match before {
            MirLocationBefore::Terminator(block) => {
                self.stmts[idx].block = Some(block);

                let old_last_stmt = self.blocks[block].last_stmt.replace(idx);

                if old_last_stmt.is_some() {
                    self.stmts[idx].prev_stmt = old_last_stmt;
                } else {
                    self.blocks[block].first_stmt = Some(idx);
                }
            }
            MirLocationBefore::Stmt(before) => {
                let block = self.stmts[before]
                    .block
                    .expect("cannot relate statements outside of a basic block");

                self.stmts[idx].block = Some(block);

                let old_prev_stmt = self.stmts[before].prev_stmt.replace(idx);

                if old_prev_stmt.is_some() {
                    self.stmts[idx].prev_stmt = old_prev_stmt;
                } else {
                    self.blocks[block].first_stmt = Some(idx);
                }
            }
        }
    }

    pub fn unlink_mir_stmt(&mut self, idx: MirStmtIdx) {
        let Some(block) = self.stmts[idx].block.take() else {
            return;
        };

        let prev_stmt = self.stmts[idx].prev_stmt.take();
        let next_stmt = self.stmts[idx].next_stmt.take();

        if let Some(prev_stmt) = prev_stmt {
            self.stmts[prev_stmt].next_stmt = next_stmt;
        } else {
            self.blocks[block].first_stmt = next_stmt;
        }

        if let Some(next_stmt) = next_stmt {
            self.stmts[next_stmt].prev_stmt = prev_stmt;
        } else {
            self.blocks[block].last_stmt = prev_stmt;
        }
    }

    pub fn block_successors(&self, idx: MirBlockIdx) -> &SmallVec<[MirBlockIdx; 2]> {
        &self.blocks[idx].successors
    }

    pub fn block_predecessors(&self, idx: MirBlockIdx) -> &SmallVec<[MirBlockIdx; 2]> {
        &self.blocks[idx].predecessors
    }

    pub fn block_first(&self, idx: MirBlockIdx) -> Option<MirStmtIdx> {
        self.blocks[idx].first_stmt
    }

    pub fn block_last(&self, idx: MirBlockIdx) -> Option<MirStmtIdx> {
        self.blocks[idx].last_stmt
    }

    pub fn stmt_block(&self, idx: MirStmtIdx) -> Option<MirBlockIdx> {
        self.stmts[idx].block
    }

    pub fn stmt_prev(&self, idx: MirStmtIdx) -> Option<MirStmtIdx> {
        self.stmts[idx].prev_stmt
    }

    pub fn stmt_next(&self, idx: MirStmtIdx) -> Option<MirStmtIdx> {
        self.stmts[idx].next_stmt
    }

    pub fn opt_stmt(&self, idx: MirStmtIdx) -> Option<&MirStmt> {
        self.stmts[idx].stmt.as_ref()
    }

    pub fn opt_stmt_mut(&mut self, idx: MirStmtIdx) -> Option<&mut MirStmt> {
        self.stmts[idx].stmt.as_mut()
    }

    pub fn stmt(&self, idx: MirStmtIdx) -> &MirStmt {
        self.opt_stmt(idx).expect("statement not initialized")
    }

    pub fn stmt_mut(&mut self, idx: MirStmtIdx) -> &mut MirStmt {
        self.opt_stmt_mut(idx).expect("statement not initialized")
    }

    pub fn set_stmt(&mut self, idx: MirStmtIdx, stmt: Option<MirStmt>) {
        self.stmts[idx].stmt = stmt;
    }

    pub fn init_stmt(&mut self, idx: MirStmtIdx, stmt: MirStmt) {
        assert!(self.opt_stmt(idx).is_none());
        self.set_stmt(idx, Some(stmt));
    }

    pub fn opt_terminator(&self, idx: MirBlockIdx) -> Option<&MirTerminator> {
        self.blocks[idx].terminator.as_ref()
    }

    pub fn opt_terminator_mut(&mut self, idx: MirBlockIdx) -> Option<&mut MirTerminator> {
        self.blocks[idx].terminator.as_mut()
    }

    pub fn terminator(&self, idx: MirBlockIdx) -> &MirTerminator {
        self.opt_terminator(idx)
            .expect("terminator not initialized")
    }

    pub fn terminator_mut(&mut self, idx: MirBlockIdx) -> &mut MirTerminator {
        self.opt_terminator_mut(idx)
            .expect("terminator not initialized")
    }

    pub fn set_terminator(&mut self, idx: MirBlockIdx, terminator: Option<MirTerminator>) {
        let new_successors = terminator.as_ref().map_or_default(|v| v.successors());

        {
            let mut check = new_successors.clone();
            check.sort_unstable();

            for [a, b] in check.array_windows() {
                assert!(a != b, "terminators cannot have duplicate successors");
            }
        }

        for successor in mem::take(&mut self.blocks[idx].successors) {
            if !self.blocks.contains_key(successor) {
                continue;
            }

            let idx = self.blocks[successor]
                .predecessors
                .iter()
                .position(|&v| v == idx)
                .unwrap();

            self.blocks[successor].predecessors.remove(idx);
        }

        for &successor in &new_successors {
            self.blocks[successor].predecessors.push(idx);
        }

        self.blocks[idx].terminator = terminator;
        self.blocks[idx].successors = new_successors;
    }

    pub fn init_terminator(&mut self, idx: MirBlockIdx, terminator: MirTerminator) {
        assert!(self.opt_terminator(idx).is_none());
        self.set_terminator(idx, Some(terminator));
    }
}

// === Definitions === //

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
            MirTerminator::UnwindResume | MirTerminator::Return | MirTerminator::Unreachable => {
                SmallVec::new()
            }
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
    Field(ResolvedFieldIdx),
}

#[derive(Debug, Clone)]
pub enum MirAssignRvalue {
    UnreachablePlaceholder,
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
    BinaryOp(MirStraightBinOpKind, Box<(MirOperand, MirOperand)>),
    UnaryOp(AstUnOpKind, MirOperand),
    Discriminant(MirPlace),
    DynUse(DynSiteIdx, MirOperand),
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

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirBinOpKind {
    Straight(MirStraightBinOpKind),
    Logical(MirLogicalBinOpKind),
}

impl MirBinOpKind {
    pub fn from_ast(op: AstBinOpKind) -> Self {
        use MirBinOpKind::*;
        use MirLogicalBinOpKind::*;
        use MirStraightBinOpKind::*;

        match op {
            AstBinOpKind::Add => Straight(Add),
            AstBinOpKind::Sub => Straight(Sub),
            AstBinOpKind::Mul => Straight(Mul),
            AstBinOpKind::Div => Straight(Div),
            AstBinOpKind::Rem => Straight(Rem),
            AstBinOpKind::BitXor => Straight(BitXor),
            AstBinOpKind::BitAnd => Straight(BitAnd),
            AstBinOpKind::BitOr => Straight(BitOr),
            AstBinOpKind::Shl => Straight(Shl),
            AstBinOpKind::Shr => Straight(Shr),
            AstBinOpKind::Eq => Straight(Eq),
            AstBinOpKind::Lt => Straight(Lt),
            AstBinOpKind::Le => Straight(Le),
            AstBinOpKind::Ne => Straight(Ne),
            AstBinOpKind::Ge => Straight(Ge),
            AstBinOpKind::Gt => Straight(Gt),
            AstBinOpKind::And => Logical(And),
            AstBinOpKind::Or => Logical(Or),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirStraightBinOpKind {
    /// The `+` operator (addition)
    Add,
    /// The `-` operator (subtraction)
    Sub,
    /// The `*` operator (multiplication)
    Mul,
    /// The `/` operator (division)
    Div,
    /// The `%` operator (modulus)
    Rem,
    /// The `^` operator (bitwise xor)
    BitXor,
    /// The `&` operator (bitwise and)
    BitAnd,
    /// The `|` operator (bitwise or)
    BitOr,
    /// The `<<` operator (shift left)
    Shl,
    /// The `>>` operator (shift right)
    Shr,
    /// The `==` operator (equality)
    Eq,
    /// The `<` operator (less than)
    Lt,
    /// The `<=` operator (less than or equal to)
    Le,
    /// The `!=` operator (not equal to)
    Ne,
    /// The `>=` operator (greater than or equal to)
    Ge,
    /// The `>` operator (greater than)
    Gt,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirLogicalBinOpKind {
    /// The `&&` operator (logical and)
    And,
    /// The `||` operator (logical or)
    Or,
}

impl MirLogicalBinOpKind {
    pub fn short_circuit_if(self) -> bool {
        match self {
            MirLogicalBinOpKind::And => false,
            MirLogicalBinOpKind::Or => true,
        }
    }

    pub fn short_circuit_value(self) -> bool {
        match self {
            MirLogicalBinOpKind::And => false,
            MirLogicalBinOpKind::Or => true,
        }
    }
}
