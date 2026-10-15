use crate::{
    base::{
        ErrorGuaranteed, Session,
        arena::{HasListInterner as _, Intern, Obj},
        syntax::Span,
    },
    parse::ast::{AstBinOpKind, AstLit, AstUnOpKind},
    semantic::syntax::{
        AdtCtor, AdtCtorOwner, AdtCtorSyntax, DynSiteIdx, Mutability, ResolvedFieldIdx, SigTy,
        TyCtxt,
    },
    utils::format::{SimpleListFormatGlue, format_list},
};
use index_vec::{IndexVec, define_index_type};
use slotmap::{SecondaryMap, SlotMap, new_key_type};
use smallvec::SmallVec;
use std::{fmt, mem, ops::ControlFlow};

// === Body === //

define_index_type! {
    pub struct MirLocalIdx = u32;
}

impl MirLocalIdx {
    pub const RETURN: Self = MirLocalIdx { _raw: 0 };
}

#[derive(Debug, Copy, Clone)]
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

impl MirBody {
    pub fn blocks<'a>(&'a self) -> impl ExactSizeIterator<Item = MirBlockRef<'a>> {
        self.cfg.blocks().map(move |id| MirBlockRef::new(self, id))
    }

    pub fn entry(&self) -> MirBlockRef<'_> {
        MirBlockRef::new(self, self.entry)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct MirBlockRef<'g> {
    pub body: &'g MirBody,
    pub block: MirBlockIdx,
}

impl<'g> MirBlockRef<'g> {
    pub fn new(body: &'g MirBody, block: MirBlockIdx) -> Self {
        Self { body, block }
    }

    pub fn stmts(self, direction: MirBodyDirection) -> impl Iterator<Item = MirStmtRef<'g>> {
        self.body
            .cfg
            .block_stmts(self.block, direction)
            .map(move |stmt| MirStmtRef::new(self.body, stmt))
    }

    pub fn first_stmt(self) -> Option<MirStmtRef<'g>> {
        self.body
            .cfg
            .block_first(self.block)
            .map(|stmt| MirStmtRef::new(self.body, stmt))
    }

    pub fn last_stmt(self) -> Option<MirStmtRef<'g>> {
        self.body
            .cfg
            .block_last(self.block)
            .map(|stmt| MirStmtRef::new(self.body, stmt))
    }

    pub fn terminator(self) -> &'g MirTerminator {
        self.body.cfg.terminator(self.block)
    }

    pub fn predecessors(self) -> &'g [MirBlockLink] {
        self.body.cfg.block_predecessors(self.block)
    }

    pub fn successors(self) -> &'g [MirBlockLink] {
        self.body.cfg.block_successors(self.block)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct MirStmtRef<'g> {
    pub body: &'g MirBody,
    pub stmt: MirStmtIdx,
}

impl<'g> MirStmtRef<'g> {
    pub fn new(body: &'g MirBody, stmt: MirStmtIdx) -> Self {
        Self { body, stmt }
    }

    pub fn block(self) -> Option<MirBlockRef<'g>> {
        self.body
            .cfg
            .stmt_block(self.stmt)
            .map(|block| MirBlockRef::new(self.body, block))
    }

    pub fn prev(self) -> Option<MirStmtRef<'g>> {
        self.body
            .cfg
            .stmt_prev(self.stmt)
            .map(|stmt| MirStmtRef::new(self.body, stmt))
    }

    pub fn next(self) -> Option<MirStmtRef<'g>> {
        self.body
            .cfg
            .stmt_next(self.stmt)
            .map(|stmt| MirStmtRef::new(self.body, stmt))
    }

    pub fn stmt(self) -> &'g MirStmt {
        self.body.cfg.stmt(self.stmt)
    }

    pub fn kind(self) -> &'g MirStmtKind {
        &self.stmt().kind
    }
}

// === Control Flow Graph === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirBodyDirection {
    Forwards,
    Backwards,
}

impl MirBodyDirection {
    pub fn is_forwards(self) -> bool {
        self == Self::Forwards
    }

    pub fn is_backwards(self) -> bool {
        self == Self::Backwards
    }
}

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

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct MirBlockLink {
    pub target: MirBlockIdx,
    pub at_idx: usize,
}

#[derive(Debug, Clone, Default)]
pub struct MirBodyCfg {
    blocks: SlotMap<MirBlockIdx, MirBlockNode>,
    stmts: SlotMap<MirStmtIdx, MirStmtNode>,
}

#[derive(Debug, Clone)]
struct MirBlockNode {
    predecessors: SmallVec<[MirBlockLink; 2]>,
    successors: SmallVec<[MirBlockLink; 2]>,
    first_stmt: Option<MirStmtIdx>,
    last_stmt: Option<MirStmtIdx>,
    terminator: Option<MirTerminator>,
}

#[derive(Debug, Clone)]
struct MirStmtNode {
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

    pub fn blocks(&self) -> impl ExactSizeIterator<Item = MirBlockIdx> {
        self.blocks.keys()
    }

    pub fn block_successors(&self, idx: MirBlockIdx) -> &[MirBlockLink] {
        &self.blocks[idx].successors
    }

    pub fn block_predecessors(&self, idx: MirBlockIdx) -> &[MirBlockLink] {
        &self.blocks[idx].predecessors
    }

    pub fn block_first(&self, idx: MirBlockIdx) -> Option<MirStmtIdx> {
        self.blocks[idx].first_stmt
    }

    pub fn block_last(&self, idx: MirBlockIdx) -> Option<MirStmtIdx> {
        self.blocks[idx].last_stmt
    }

    pub fn block_stmts_interactive(
        &self,
        idx: MirBlockIdx,
        direction: MirBodyDirection,
    ) -> MirStmtIterInteractive {
        MirStmtIterInteractive::new(self, idx, direction)
    }

    pub fn block_stmts(&self, idx: MirBlockIdx, direction: MirBodyDirection) -> MirStmtIter<'_> {
        MirStmtIter::new(self, idx, direction)
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
        let new_successors = terminator.as_ref().map_or_default(|v| {
            v.successors()
                .into_iter()
                .map(|v| v.target)
                .collect::<SmallVec<[MirBlockIdx; 2]>>()
        });

        // Validate successors
        {
            let mut check = new_successors.clone();
            check.sort_unstable();

            for &a in &check {
                assert!(a != idx);
            }

            for [a, b] in check.array_windows() {
                assert!(a != b, "terminators cannot have duplicate successors");
            }
        }

        // Unlink from existing successors' predecessor lists.
        for MirBlockLink {
            target: successor,
            at_idx: remove_at_idx,
        } in mem::take(&mut self.blocks[idx].successors)
        {
            let Some(successor) = self.blocks.get_mut(successor) else {
                continue;
            };

            successor.predecessors.swap_remove(remove_at_idx);

            if let Some(&patched) = successor.predecessors.get(remove_at_idx) {
                self.blocks[patched.target].successors[patched.at_idx].at_idx = remove_at_idx;
            }
        }

        // Register into new successors' predecessor lists.
        let new_successors = new_successors
            .into_iter()
            .enumerate()
            .map(|(back_at_idx, successor)| {
                let successor_data = &mut self.blocks[successor];

                let fwd_at_idx = successor_data.predecessors.len();

                successor_data.predecessors.push(MirBlockLink {
                    target: idx,
                    at_idx: back_at_idx,
                });

                MirBlockLink {
                    target: successor,
                    at_idx: fwd_at_idx,
                }
            })
            .collect::<SmallVec<[_; 2]>>();

        // Update self.
        self.blocks[idx].terminator = terminator;
        self.blocks[idx].successors = new_successors;
    }

    pub fn init_terminator(&mut self, idx: MirBlockIdx, terminator: MirTerminator) {
        assert!(self.opt_terminator(idx).is_none());
        self.set_terminator(idx, Some(terminator));
    }

    pub fn prune_unreachable(&mut self, entry: MirBlockIdx) {
        let mut live_scopes = SecondaryMap::from_iter([(entry, ())]);
        let mut stack = Vec::from_iter([entry]);

        while let Some(curr) = stack.pop() {
            assert!(
                self.opt_terminator(curr).is_some(),
                "{curr:?} is missing a terminator",
            );

            for successor in self.block_successors(curr) {
                if live_scopes.insert(successor.target, ()).is_none() {
                    stack.push(successor.target);
                }
            }
        }

        self.blocks.retain(|key, _| live_scopes.contains_key(key));
    }
}

#[derive(Debug, Clone)]
pub struct MirStmtIterInteractive {
    direction: MirBodyDirection,
    next: Option<MirStmtIdx>,
}

impl MirStmtIterInteractive {
    pub fn new(cfg: &MirBodyCfg, block: MirBlockIdx, direction: MirBodyDirection) -> Self {
        Self {
            direction,
            next: match direction {
                MirBodyDirection::Forwards => cfg.block_first(block),
                MirBodyDirection::Backwards => cfg.block_last(block),
            },
        }
    }

    pub fn next(&mut self, cfg: &MirBodyCfg) -> Option<MirStmtIdx> {
        let curr = self.next?;

        self.next = match self.direction {
            MirBodyDirection::Forwards => cfg.stmt_next(curr),
            MirBodyDirection::Backwards => cfg.stmt_prev(curr),
        };

        Some(curr)
    }
}

#[derive(Debug, Clone)]
pub struct MirStmtIter<'a> {
    cfg: &'a MirBodyCfg,
    iter: MirStmtIterInteractive,
}

impl<'a> MirStmtIter<'a> {
    pub fn new(cfg: &'a MirBodyCfg, block: MirBlockIdx, direction: MirBodyDirection) -> Self {
        Self {
            cfg,
            iter: MirStmtIterInteractive::new(cfg, block, direction),
        }
    }
}

impl Iterator for MirStmtIter<'_> {
    type Item = MirStmtIdx;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next(self.cfg)
    }
}

// === Statement === //

#[derive(Debug, Clone)]
pub struct MirStmt {
    pub source_info: MirStmtSourceInfo,
    pub kind: MirStmtKind,
}

#[derive(Debug, Copy, Clone)]
pub enum MirStmtSourceInfo {
    Simple(Span),
    Break,
    Local,
}

#[derive(Debug, Clone)]
pub enum MirStmtKind {
    StorageLive(MirLocalIdx),
    StorageDead(MirLocalIdx),
    Assign(Box<(MirPlace, MirRvalue)>),
    DiscardWithoutDrop(MirRvalue),
}

impl TraverseMentions for MirStmtKind {
    fn traverse_mentions<B>(
        tcx: &TyCtxt,
        me: &Self,
        f: &mut impl FnMut(MirPlaceMention) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        match me {
            MirStmtKind::StorageLive(local) => {
                f(MirPlaceMention {
                    kind: MirPlaceMentionKind::STORAGE_LIVE,
                    place: MirPlace::new(tcx, *local, []),
                })?;
            }
            MirStmtKind::StorageDead(local) => {
                f(MirPlaceMention {
                    kind: MirPlaceMentionKind::STORAGE_DEAD,
                    place: MirPlace::new(tcx, *local, []),
                })?;
            }
            MirStmtKind::Assign(assign) => {
                let (lhs, rhs) = &**assign;

                TraverseMentions::traverse_mentions(tcx, rhs, f)?;

                f(MirPlaceMention {
                    kind: MirPlaceMentionKind::INIT,
                    place: *lhs,
                })?;
            }
            MirStmtKind::DiscardWithoutDrop(rvalue) => {
                TraverseMentions::traverse_mentions(tcx, rvalue, f)?;
            }
        }

        ControlFlow::Continue(())
    }
}

#[derive(Debug, Clone)]
pub enum MirRvalue {
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

impl TraverseMentions for MirRvalue {
    fn traverse_mentions<B>(
        tcx: &TyCtxt,
        me: &Self,
        f: &mut impl FnMut(MirPlaceMention) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        match me {
            MirRvalue::UnreachablePlaceholder
            | MirRvalue::Error(_)
            | MirRvalue::Zst(_)
            | MirRvalue::Literal(_, _) => {
                // (empty)
            }
            MirRvalue::Tuple(operands) => {
                TraverseMentions::traverse_mentions_iter(tcx, operands, f)?;
            }
            MirRvalue::Adt(_adt, operands) => {
                TraverseMentions::traverse_mentions_iter(tcx, operands, f)?;
            }
            MirRvalue::Use(operand) => {
                TraverseMentions::traverse_mentions(tcx, operand, f)?;
            }
            MirRvalue::MoveOutRef {
                can_move_from,
                ref_place,
            } => {
                f(MirPlaceMention {
                    kind: MirPlaceMentionKind::MOVED,
                    place: *ref_place,
                })?;

                for can_move_from in can_move_from {
                    f(MirPlaceMention {
                        kind: MirPlaceMentionKind::MOVED,
                        place: *can_move_from,
                    })?;
                }
            }
            MirRvalue::Ref(_muta, place) => {
                f(MirPlaceMention {
                    kind: MirPlaceMentionKind::READ,
                    place: *place,
                })?;
            }
            MirRvalue::BinaryOp(_kind, operands) => {
                TraverseMentions::traverse_mentions(tcx, &operands.0, f)?;
                TraverseMentions::traverse_mentions(tcx, &operands.1, f)?;
            }
            MirRvalue::UnaryOp(_kind, operand) => {
                TraverseMentions::traverse_mentions(tcx, operand, f)?;
            }
            MirRvalue::Discriminant(place) => {
                f(MirPlaceMention {
                    kind: MirPlaceMentionKind::READ,
                    place: *place,
                })?;
            }
            MirRvalue::DynUse(_site, operand) => {
                TraverseMentions::traverse_mentions(tcx, operand, f)?;
            }
        }

        ControlFlow::Continue(())
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

impl MirStraightBinOpKind {
    pub fn to_ast(self) -> AstBinOpKind {
        match self {
            MirStraightBinOpKind::Add => AstBinOpKind::Add,
            MirStraightBinOpKind::Sub => AstBinOpKind::Sub,
            MirStraightBinOpKind::Mul => AstBinOpKind::Mul,
            MirStraightBinOpKind::Div => AstBinOpKind::Div,
            MirStraightBinOpKind::Rem => AstBinOpKind::Rem,
            MirStraightBinOpKind::BitXor => AstBinOpKind::BitXor,
            MirStraightBinOpKind::BitAnd => AstBinOpKind::BitAnd,
            MirStraightBinOpKind::BitOr => AstBinOpKind::BitOr,
            MirStraightBinOpKind::Shl => AstBinOpKind::Shl,
            MirStraightBinOpKind::Shr => AstBinOpKind::Shr,
            MirStraightBinOpKind::Eq => AstBinOpKind::Eq,
            MirStraightBinOpKind::Lt => AstBinOpKind::Lt,
            MirStraightBinOpKind::Le => AstBinOpKind::Le,
            MirStraightBinOpKind::Ne => AstBinOpKind::Ne,
            MirStraightBinOpKind::Ge => AstBinOpKind::Ge,
            MirStraightBinOpKind::Gt => AstBinOpKind::Gt,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirLogicalBinOpKind {
    /// The `&&` operator (logical and)
    And,
    /// The `||` operator (logical or)
    Or,
}

impl MirLogicalBinOpKind {
    pub fn to_ast(self) -> AstBinOpKind {
        match self {
            MirLogicalBinOpKind::And => AstBinOpKind::And,
            MirLogicalBinOpKind::Or => AstBinOpKind::Or,
        }
    }

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

// === Terminator === //

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
    Unreachable,
    Return,
    UnwindResume,
}

impl TraverseMentions for MirTerminator {
    fn traverse_mentions<B>(
        tcx: &TyCtxt,
        me: &Self,
        f: &mut impl FnMut(MirPlaceMention) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        match me {
            MirTerminator::Goto(_)
            | MirTerminator::Unreachable
            | MirTerminator::Return
            | MirTerminator::UnwindResume => {
                // (no mentions)
            }
            MirTerminator::SwitchInt {
                discr,
                constants: _,
                targets: _,
            } => {
                TraverseMentions::traverse_mentions(tcx, discr, f)?;
            }
            MirTerminator::Call {
                callee,
                args,
                destination,
                target: _,
                unwind: _,
            } => {
                TraverseMentions::traverse_mentions(tcx, callee, f)?;
                TraverseMentions::traverse_mentions_iter(tcx, args, f)?;

                f(MirPlaceMention {
                    kind: MirPlaceMentionKind::INIT,
                    place: *destination,
                })?;
            }
            MirTerminator::EnsureDropped {
                place,
                target: _,
                unwind: _,
            } => {
                f(MirPlaceMention {
                    kind: MirPlaceMentionKind::INVALIDATED,
                    place: *place,
                })?;
            }
        }

        ControlFlow::Continue(())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct MirTerminatorSuccessor {
    pub target: MirBlockIdx,
    pub is_unwind: bool,
}

impl MirTerminator {
    pub fn successors(&self) -> SmallVec<[MirTerminatorSuccessor; 2]> {
        match *self {
            MirTerminator::Goto(target) => SmallVec::from_iter([MirTerminatorSuccessor {
                target,
                is_unwind: false,
            }]),
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
            } => SmallVec::from_iter(
                [MirTerminatorSuccessor {
                    target,
                    is_unwind: false,
                }]
                .into_iter()
                .chain(unwind.block().map(|target| MirTerminatorSuccessor {
                    target,
                    is_unwind: true,
                })),
            ),
            MirTerminator::SwitchInt {
                discr: _,
                constants: _,
                ref targets,
            } => {
                SmallVec::from_iter(
                    targets
                        .iter()
                        .copied()
                        .map(|target| MirTerminatorSuccessor {
                            target,
                            is_unwind: false,
                        }),
                )
            }
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

// === Operand === //

pub trait TraverseMentions: Sized {
    fn traverse_mentions<B>(
        tcx: &TyCtxt,
        me: &Self,
        f: &mut impl FnMut(MirPlaceMention) -> ControlFlow<B>,
    ) -> ControlFlow<B>;

    fn traverse_mentions_iter<'a, B>(
        tcx: &TyCtxt,
        me: impl IntoIterator<Item = &'a Self>,
        f: &mut impl FnMut(MirPlaceMention) -> ControlFlow<B>,
    ) -> ControlFlow<B>
    where
        Self: 'a,
    {
        for me in me {
            Self::traverse_mentions(tcx, me, f)?;
        }

        ControlFlow::Continue(())
    }

    fn iter_mentions<B>(
        &self,
        tcx: &TyCtxt,
        mut f: impl FnMut(MirPlaceMention) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        Self::traverse_mentions(tcx, self, &mut f)
    }

    fn mentions(&self, tcx: &TyCtxt) -> SmallVec<[MirPlaceMention; 4]> {
        let mut collector = SmallVec::new();

        cbit::cbit! {
            for mention in self.iter_mentions(tcx) {
                collector.push(mention);
            }
        }

        collector
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct MirPlaceMention {
    pub kind: MirPlaceMentionKind,
    pub place: MirPlace,
}

bitflags::bitflags! {
    #[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
    pub struct MirPlaceMentionKind: u32 {
        const LIVENESS_USE = Self::MOVED.bits() | Self::READ.bits();
        const LIVENESS_INIT = Self::INIT.bits();

        /// Invalidates the place without requiring it to be occupied.
        const INVALIDATED = 1 << 0;

        /// Requires the place to be occupied and moves it out.
        const MOVED = 1 << 2;

        /// Requires the place to be occupied and simply reads it.
        const READ = 1 << 3;

        /// Always initializes the place to a complete value unless the unwind path was taken.
        const INIT = 1 << 4;

        /// A `StorageLive` statement.
        const STORAGE_LIVE = 1 << 5;

        /// A `StorageDead` statement.
        const STORAGE_DEAD = 1 << 6;
    }
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

impl TraverseMentions for MirOperand {
    fn traverse_mentions<B>(
        _tcx: &TyCtxt,
        me: &Self,
        f: &mut impl FnMut(MirPlaceMention) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        match *me {
            MirOperand::Copy(place) => f(MirPlaceMention {
                kind: MirPlaceMentionKind::READ,
                place,
            }),
            MirOperand::Move(place) => f(MirPlaceMention {
                kind: MirPlaceMentionKind::MOVED,
                place,
            }),
        }
    }
}

impl MirOperand {
    pub fn place(self) -> MirPlace {
        let (MirOperand::Copy(place) | MirOperand::Move(place)) = self;

        place
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

// === Pretty === //

pub struct MirPrettyFmtCx<'a> {
    tcx: &'a TyCtxt,
    body: &'a MirBody,
}

impl<'a> MirPrettyFmtCx<'a> {
    pub fn new(tcx: &'a TyCtxt, body: &'a MirBody) -> Self {
        Self { tcx, body }
    }

    pub fn wrap<T>(&self, value: T) -> MirPrettyFmt<'_, T> {
        MirPrettyFmt { cx: self, value }
    }

    pub fn tcx(&self) -> &'a TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'a Session {
        &self.tcx.session
    }

    pub fn body(&self) -> &'a MirBody {
        self.body
    }
}

pub struct MirPrettyFmt<'a, T> {
    cx: &'a MirPrettyFmtCx<'a>,
    value: T,
}

impl fmt::Display for MirPrettyFmt<'_, MirLocalIdx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.value.index())
    }
}

impl fmt::Display for MirPrettyFmt<'_, MirPlace> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();

        self.cx.wrap(self.value.local).fmt(f)?;

        for elem in self.value.projections.r(s) {
            match elem {
                MirPlaceElem::DerefPtr => {
                    write!(f, ".*")?;
                }
                MirPlaceElem::Field(ResolvedFieldIdx::Adt(adt, idx)) => {
                    match adt.r(s).owner {
                        AdtCtorOwner::Struct(_) => {
                            // (no coercion)
                        }
                        AdtCtorOwner::EnumVariant(variant) => {
                            write!(f, ".as<{}>", variant.r(s).ident.text)?;
                        }
                    }

                    match &adt.r(s).syntax {
                        AdtCtorSyntax::Unit => unreachable!(),
                        AdtCtorSyntax::Tuple => {
                            write!(f, ".{}", idx.index())?;
                        }
                        AdtCtorSyntax::Named(_) => {
                            write!(f, ".{}", adt.r(s).fields[*idx].ident.unwrap().text)?;
                        }
                    }
                }
                MirPlaceElem::Field(ResolvedFieldIdx::Tuple { field_idx, .. }) => {
                    write!(f, ".{field_idx}")?;
                }
            }
        }

        Ok(())
    }
}

impl fmt::Display for MirPrettyFmt<'_, MirOperand> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            MirOperand::Copy(place) => write!(f, "copy({})", self.cx.wrap(place)),
            MirOperand::Move(place) => write!(f, "move({})", self.cx.wrap(place)),
        }
    }
}

impl fmt::Display for MirPrettyFmt<'_, &MirRvalue> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();

        match self.value {
            MirRvalue::UnreachablePlaceholder => {
                write!(f, "unreachable")?;
            }
            MirRvalue::Tuple(operands) => {
                if let [unique] = **operands {
                    write!(f, "({},)", self.cx.wrap(unique))?;
                } else {
                    write!(
                        f,
                        "({})",
                        format_list(
                            operands.iter().map(|&op| self.cx.wrap(op)),
                            SimpleListFormatGlue::COMMA_LIST
                        )
                    )?;
                }
            }
            MirRvalue::Adt(ctor, operands) => match &ctor.r(s).syntax {
                AdtCtorSyntax::Unit => {
                    assert!(operands.is_empty());

                    write!(f, "{}", ctor.r(s).owner.path(s))?;
                }
                AdtCtorSyntax::Tuple => {
                    write!(
                        f,
                        "{}({})",
                        ctor.r(s).owner.path(s),
                        format_list(
                            operands.iter().map(|&op| self.cx.wrap(op)),
                            SimpleListFormatGlue::COMMA_LIST
                        )
                    )?;
                }
                AdtCtorSyntax::Named(_) => {
                    write!(
                        f,
                        "{} {{ {} }}",
                        ctor.r(s).owner.path(s),
                        format_list(
                            operands.iter().enumerate().map(|(idx, &op)| {
                                format!(
                                    "{}: {}",
                                    ctor.r(s).fields[idx].ident.unwrap().text,
                                    self.cx.wrap(op)
                                )
                            }),
                            SimpleListFormatGlue::COMMA_LIST
                        )
                    )?;
                }
            },
            MirRvalue::Use(operand) => {
                write!(f, "use({})", self.cx.wrap(*operand))?;
            }
            MirRvalue::MoveOutRef {
                can_move_from,
                ref_place,
            } => {
                write!(
                    f,
                    "late-move(*{}, possibly [{}])",
                    self.cx.wrap(*ref_place),
                    format_list(
                        can_move_from.iter().map(|&place| self.cx.wrap(place)),
                        SimpleListFormatGlue::COMMA_LIST
                    )
                )?;
            }
            MirRvalue::Ref(muta, place) => {
                write!(f, "&{}{}", muta.opt_space_qual(), self.cx.wrap(*place))?;
            }
            MirRvalue::Zst(ty) => {
                write!(f, "zst({})", self.cx.wrap(*ty))?;
            }
            MirRvalue::Literal(ty, lit) => {
                write!(f, "{} :: {}", self.cx.wrap(*lit), self.cx.wrap(*ty))?;
            }
            MirRvalue::BinaryOp(kind, operands) => {
                write!(
                    f,
                    "{} {} {}",
                    self.cx.wrap(operands.0),
                    kind.to_ast().punct().bare_name(),
                    self.cx.wrap(operands.1)
                )?;
            }
            MirRvalue::UnaryOp(kind, operand) => {
                write!(f, "{}{}", kind.punct().bare_name(), self.cx.wrap(*operand))?;
            }
            MirRvalue::Discriminant(place) => {
                write!(f, "discriminant({})", self.cx.wrap(*place))?;
            }
            MirRvalue::DynUse(_site, operand) => {
                write!(f, "dyn-use({})", self.cx.wrap(*operand))?;
            }
            MirRvalue::Error(_) => {
                write!(f, "error")?;
            }
        }

        Ok(())
    }
}

impl fmt::Display for MirPrettyFmt<'_, SigTy> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO
        // write!(f, "{:?}", self.value)
        f.write_str("<type>")
    }
}

impl fmt::Display for MirPrettyFmt<'_, AstLit> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO
        write!(f, "{:?}", self.value)
    }
}

impl fmt::Display for MirPrettyFmt<'_, &MirStmt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}  // {}",
            self.cx.wrap(&self.value.kind),
            self.cx.wrap(self.value.source_info)
        )
    }
}

impl fmt::Display for MirPrettyFmt<'_, MirStmtSourceInfo> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO
        write!(f, "{:?}", self.value)
    }
}

impl fmt::Display for MirPrettyFmt<'_, &MirStmtKind> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.value {
            MirStmtKind::StorageLive(local) => {
                write!(f, "storage-live({});", self.cx.wrap(*local))?;
            }
            MirStmtKind::StorageDead(local) => {
                write!(f, "storage-dead({});", self.cx.wrap(*local))?;
            }
            MirStmtKind::Assign(stmt) => {
                write!(f, "{} = {};", self.cx.wrap(stmt.0), self.cx.wrap(&stmt.1))?;
            }
            MirStmtKind::DiscardWithoutDrop(rvalue) => {
                write!(f, "dropless _ = {};", self.cx.wrap(rvalue))?;
            }
        }

        Ok(())
    }
}
