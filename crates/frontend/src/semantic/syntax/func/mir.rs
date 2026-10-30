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
    utils::format::{IndentedFmt, SimpleListFormatGlue, fmt_write, format_list},
};
use index_vec::{IndexVec, define_index_type};
use slotmap::{SecondaryMap, SlotMap, new_key_type};
use smallvec::SmallVec;
use std::{
    fmt::{self, Display as _, Write as _},
    mem,
    ops::ControlFlow,
};

// === Source Info === //

define_index_type! {
    pub struct MirScopeIdx = u32;
}

impl MirScopeIdx {
    pub const ENTRY: Self = MirScopeIdx { _raw: 0 };

    pub const UNCATEGORIZED: Self = MirScopeIdx { _raw: u32::MAX };
}

#[derive(Debug, Copy, Clone)]
pub enum MirSourceInfo {
    Todo,
    Simple(Span),
    ExprDivergent,
    BlockFallthrough,
    Local(MirLocalIdx),
}

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
    pub arg_count: u32,
    pub entry: MirBlockIdx,
    pub cfg: MirBodyCfg,
}

impl Default for MirBody {
    fn default() -> Self {
        Self {
            locals: IndexVec::default(),
            arg_count: 0,
            entry: MirBlockIdx::default(),
            cfg: MirBodyCfg::default(),
        }
    }
}

impl MirBody {
    pub fn blocks<'a>(&'a self) -> impl ExactSizeIterator<Item = MirBlockRef<'a>> {
        self.cfg.blocks().map(move |id| MirBlockRef::new(self, id))
    }

    pub fn arg_locals(&self) -> impl ExactSizeIterator<Item = MirLocalIdx> {
        (1..self.arg_count + 1).map(MirLocalIdx::from_raw)
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
            .block_natural_first(self.block)
            .map(|stmt| MirStmtRef::new(self.body, stmt))
    }

    pub fn last_stmt(self) -> Option<MirStmtRef<'g>> {
        self.body
            .cfg
            .block_natural_last(self.block)
            .map(|stmt| MirStmtRef::new(self.body, stmt))
    }

    pub fn opt_terminator(self) -> Option<&'g MirTerminator> {
        self.body.cfg.opt_terminator(self.block)
    }

    pub fn terminator(self) -> &'g MirTerminator {
        self.body.cfg.terminator(self.block)
    }

    pub fn terminator_kind(self) -> &'g MirTerminatorKind {
        &self.terminator().kind
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
            .stmt_natural_prev(self.stmt)
            .map(|stmt| MirStmtRef::new(self.body, stmt))
    }

    pub fn next(self) -> Option<MirStmtRef<'g>> {
        self.body
            .cfg
            .stmt_natural_next(self.stmt)
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
        self == MirBodyDirection::Forwards
    }

    pub fn is_backwards(self) -> bool {
        self == MirBodyDirection::Backwards
    }

    pub fn flip(self) -> Self {
        match self {
            MirBodyDirection::Forwards => MirBodyDirection::Backwards,
            MirBodyDirection::Backwards => MirBodyDirection::Forwards,
        }
    }
}

new_key_type! {
    pub struct MirBlockIdx;

    pub struct MirStmtIdx;
}

impl fmt::Display for MirBlockIdx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{:?}", self.0)
    }
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

    pub fn delete_block(&mut self, block: MirBlockIdx) {
        self.set_terminator(block, None);
        self.blocks.remove(block);
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
        self.move_single_stmt_before(idx, MirLocationBefore::Terminator(block));
        self.init_stmt(idx, stmt);
        idx
    }

    pub fn after_to_before(&self, after: MirLocationAfter) -> MirLocationBefore {
        match after {
            MirLocationAfter::BlockStart(block) => match self.block_natural_first(block) {
                Some(first) => MirLocationBefore::Stmt(first),
                None => MirLocationBefore::Terminator(block),
            },
            MirLocationAfter::Stmt(after_stmt) => match self.stmt_natural_next(after_stmt) {
                Some(subsequent) => MirLocationBefore::Stmt(subsequent),
                None => MirLocationBefore::Terminator(self.stmt_block(after_stmt).unwrap()),
            },
        }
    }

    pub fn before_to_after(&self, before: MirLocationBefore) -> MirLocationAfter {
        match before {
            MirLocationBefore::Terminator(block) => match self.block_natural_last(block) {
                Some(last) => MirLocationAfter::Stmt(last),
                None => MirLocationAfter::BlockStart(block),
            },
            MirLocationBefore::Stmt(before_stmt) => match self.stmt_natural_prev(before_stmt) {
                Some(predecessor) => MirLocationAfter::Stmt(predecessor),
                None => MirLocationAfter::BlockStart(self.stmt_block(before_stmt).unwrap()),
            },
        }
    }

    pub fn move_single_stmt_after(&mut self, idx: MirStmtIdx, after: MirLocationAfter) {
        self.move_single_stmt_before(idx, self.after_to_before(after));
    }

    pub fn move_single_stmt_before(&mut self, idx: MirStmtIdx, before: MirLocationBefore) {
        self.unlink_single_mir_stmt(idx);

        match before {
            MirLocationBefore::Terminator(block) => {
                self.stmts[idx].block = Some(block);

                // idx <- block
                // idx -> block handled implicitly
                let old_last_stmt = self.blocks[block].last_stmt.replace(idx);

                // prev <- idx
                self.stmts[idx].prev_stmt = old_last_stmt;

                // prev -> idx
                if let Some(old_last_stmt) = old_last_stmt {
                    self.stmts[old_last_stmt].next_stmt = Some(idx);
                } else {
                    self.blocks[block].first_stmt = Some(idx);
                }
            }
            MirLocationBefore::Stmt(before) => {
                let block = self.stmts[before]
                    .block
                    .expect("cannot relate statements outside of a basic block");

                self.stmts[idx].block = Some(block);

                // idx <- before
                let old_prev_stmt = self.stmts[before].prev_stmt.replace(idx);

                // idx -> before
                self.stmts[idx].next_stmt = Some(before);

                // old_prev_stmt <- idx
                self.stmts[idx].prev_stmt = old_prev_stmt;

                // old_prev_stmt -> idx
                if let Some(old_prev_stmt) = old_prev_stmt {
                    self.stmts[old_prev_stmt].next_stmt = Some(idx);
                } else {
                    self.blocks[block].first_stmt = Some(idx);
                }
            }
        }
    }

    pub fn unlink_single_mir_stmt(&mut self, idx: MirStmtIdx) {
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

    pub fn block_natural_first(&self, idx: MirBlockIdx) -> Option<MirStmtIdx> {
        self.blocks[idx].first_stmt
    }

    pub fn block_natural_last(&self, idx: MirBlockIdx) -> Option<MirStmtIdx> {
        self.blocks[idx].last_stmt
    }

    pub fn block_dir_first(
        &self,
        direction: MirBodyDirection,
        idx: MirBlockIdx,
    ) -> Option<MirStmtIdx> {
        match direction {
            MirBodyDirection::Forwards => self.block_natural_first(idx),
            MirBodyDirection::Backwards => self.block_natural_last(idx),
        }
    }

    pub fn block_dir_last(
        &self,
        direction: MirBodyDirection,
        idx: MirBlockIdx,
    ) -> Option<MirStmtIdx> {
        self.block_dir_first(direction.flip(), idx)
    }

    pub fn stmts_after_inclusive_interactive(
        &self,
        stmt: Option<MirStmtIdx>,
        direction: MirBodyDirection,
    ) -> MirStmtIterInteractive {
        MirStmtIterInteractive::new(stmt, direction)
    }

    pub fn stmts_after_inclusive(
        &self,
        stmt: Option<MirStmtIdx>,
        direction: MirBodyDirection,
    ) -> MirStmtIter<'_> {
        self.stmts_after_inclusive_interactive(stmt, direction)
            .wrap(self)
    }

    pub fn stmts_after_exclusive_interactive(
        &self,
        stmt: Option<MirStmtIdx>,
        direction: MirBodyDirection,
    ) -> MirStmtIterInteractive {
        self.stmts_after_inclusive_interactive(
            stmt.and_then(|stmt| self.stmt_dir_next(direction, stmt)),
            direction,
        )
    }

    pub fn stmts_after_exclusive(
        &self,
        stmt: Option<MirStmtIdx>,
        direction: MirBodyDirection,
    ) -> MirStmtIter<'_> {
        self.stmts_after_exclusive_interactive(stmt, direction)
            .wrap(self)
    }

    pub fn block_stmts_interactive(
        &self,
        block: MirBlockIdx,
        direction: MirBodyDirection,
    ) -> MirStmtIterInteractive {
        self.stmts_after_inclusive_interactive(self.block_dir_first(direction, block), direction)
    }

    pub fn block_stmts(&self, block: MirBlockIdx, direction: MirBodyDirection) -> MirStmtIter<'_> {
        self.block_stmts_interactive(block, direction).wrap(self)
    }

    pub fn stmt_block(&self, idx: MirStmtIdx) -> Option<MirBlockIdx> {
        self.stmts[idx].block
    }

    pub fn stmt_natural_prev(&self, idx: MirStmtIdx) -> Option<MirStmtIdx> {
        self.stmts[idx].prev_stmt
    }

    pub fn stmt_natural_next(&self, idx: MirStmtIdx) -> Option<MirStmtIdx> {
        self.stmts[idx].next_stmt
    }

    pub fn stmt_dir_prev(
        &self,
        direction: MirBodyDirection,
        idx: MirStmtIdx,
    ) -> Option<MirStmtIdx> {
        self.stmt_dir_next(direction.flip(), idx)
    }

    pub fn stmt_dir_next(
        &self,
        direction: MirBodyDirection,
        idx: MirStmtIdx,
    ) -> Option<MirStmtIdx> {
        match direction {
            MirBodyDirection::Forwards => self.stmt_natural_next(idx),
            MirBodyDirection::Backwards => self.stmt_natural_prev(idx),
        }
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
            v.kind
                .successors()
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
                "{curr} is missing a terminator",
            );

            for successor in self.block_successors(curr) {
                if live_scopes.insert(successor.target, ()).is_none() {
                    stack.push(successor.target);
                }
            }
        }

        let mut victims = self.blocks().collect::<Vec<_>>();
        victims.retain(|victim| !live_scopes.contains_key(*victim));

        for victim in victims {
            self.delete_block(victim);
        }
    }
}

#[derive(Debug, Clone)]
pub struct MirStmtIterInteractive {
    direction: MirBodyDirection,
    next: Option<MirStmtIdx>,
}

impl MirStmtIterInteractive {
    pub fn new(first: Option<MirStmtIdx>, direction: MirBodyDirection) -> Self {
        Self {
            direction,
            next: first,
        }
    }

    pub fn wrap<'a>(self, cfg: &'a MirBodyCfg) -> MirStmtIter<'a> {
        MirStmtIter::new(cfg, self)
    }

    pub fn next(&mut self, cfg: &MirBodyCfg) -> Option<MirStmtIdx> {
        let curr = self.next?;
        self.next = cfg.stmt_dir_next(self.direction, curr);

        Some(curr)
    }
}

#[derive(Debug, Clone)]
pub struct MirStmtIter<'a> {
    cfg: &'a MirBodyCfg,
    iter: MirStmtIterInteractive,
}

impl<'a> MirStmtIter<'a> {
    pub fn new(cfg: &'a MirBodyCfg, iter: MirStmtIterInteractive) -> Self {
        Self { cfg, iter }
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
    pub source_info: MirSourceInfo,
    pub kind: MirStmtKind,
}

#[derive(Debug, Clone)]
pub enum MirStmtKind {
    StorageLive(MirLocalIdx),
    StorageDead(MirLocalIdx),
    Assign(Box<(MirPlace, MirRvalue)>),
    Discard(Box<(SigTy, MirRvalue)>),
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
            MirStmtKind::Assign(stmt) => {
                let (lhs, rhs) = &**stmt;

                TraverseMentions::traverse_mentions(tcx, rhs, f)?;

                f(MirPlaceMention {
                    kind: MirPlaceMentionKind::INIT,
                    place: *lhs,
                })?;
            }
            MirStmtKind::Discard(stmt) => {
                let (_ty, rhs) = &**stmt;

                TraverseMentions::traverse_mentions(tcx, rhs, f)?;
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
    UnaryOp(MirStraightUnOpKind, MirOperand),
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

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirUnOpKind {
    Straight(MirStraightUnOpKind),
    /// The `*` operator for dereferencing.
    Deref,
}

impl MirUnOpKind {
    pub fn from_ast(op: AstUnOpKind) -> Self {
        use MirStraightUnOpKind::*;
        use MirUnOpKind::*;

        match op {
            AstUnOpKind::Deref => Deref,
            AstUnOpKind::Not => Straight(Not),
            AstUnOpKind::Neg => Straight(Neg),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirStraightUnOpKind {
    /// The `!` operator for logical inversion
    Not,
    /// The `-` operator for negation
    Neg,
}

impl MirStraightUnOpKind {
    pub fn to_ast(self) -> AstUnOpKind {
        match self {
            MirStraightUnOpKind::Not => AstUnOpKind::Not,
            MirStraightUnOpKind::Neg => AstUnOpKind::Neg,
        }
    }
}

// === Terminator === //

#[derive(Debug, Clone)]
pub struct MirTerminator {
    pub debug_scope: MirScopeIdx,
    pub source_info: MirSourceInfo,
    pub kind: MirTerminatorKind,
}

#[derive(Debug, Clone)]
pub enum MirTerminatorKind {
    Goto(MirBlockIdx),
    SwitchInt {
        discr: MirOperand,
        constants: SmallVec<[u64; 2]>,
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

impl TraverseMentions for MirTerminatorKind {
    fn traverse_mentions<B>(
        tcx: &TyCtxt,
        me: &Self,
        f: &mut impl FnMut(MirPlaceMention) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        match me {
            MirTerminatorKind::Goto(_)
            | MirTerminatorKind::Unreachable
            | MirTerminatorKind::Return
            | MirTerminatorKind::UnwindResume => {
                // (no mentions)
            }
            MirTerminatorKind::SwitchInt {
                discr,
                constants: _,
                targets: _,
            } => {
                TraverseMentions::traverse_mentions(tcx, discr, f)?;
            }
            MirTerminatorKind::Call {
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
            MirTerminatorKind::EnsureDropped {
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

impl MirTerminatorKind {
    pub fn successors(&self) -> SmallVec<[MirTerminatorSuccessor; 2]> {
        match *self {
            MirTerminatorKind::Goto(target) => SmallVec::from_iter([MirTerminatorSuccessor {
                target,
                is_unwind: false,
            }]),
            MirTerminatorKind::Call {
                callee: _,
                args: _,
                destination: _,
                target,
                unwind,
            }
            | MirTerminatorKind::EnsureDropped {
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
            MirTerminatorKind::SwitchInt {
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
            MirTerminatorKind::UnwindResume
            | MirTerminatorKind::Return
            | MirTerminatorKind::Unreachable => SmallVec::new(),
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

        const OCCUPANCY_ADD = Self::INIT.bits();
        const OCCUPANCY_DEAD = Self::INVALIDATED.bits() | Self::MOVED.bits() | Self::STORAGE_DEAD.bits();
        const OCCUPANCY_ACCESS = Self::MOVED.bits() | Self::READ.bits();

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

    pub fn is_move(self) -> bool {
        self == Self::Move
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

    pub fn truncate_to_len(self, tcx: &TyCtxt, len: usize) -> Self {
        let s = &tcx.session;

        Self::new(
            tcx,
            self.local,
            self.projections.r(s)[..len].iter().copied(),
        )
    }
}

pub type MirPlaceElemList = Intern<[MirPlaceElem]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirPlaceElem {
    DerefPtr,
    Field(ResolvedFieldIdx),
}

// === Pretty === //

#[derive(Copy, Clone)]
pub struct MirPrettyFmt<'a> {
    pub tcx: &'a TyCtxt,
    pub body: &'a MirBody,
    pub hooks: &'a (dyn 'a + MirPrettyFmtHooks),
}

pub trait MirPrettyFmtHooks {
    fn start_of_block(
        &self,
        cx: &MirPrettyFmt<'_>,
        f: &mut fmt::Formatter<'_>,
        block: MirBlockIdx,
    ) -> fmt::Result {
        _ = (cx, f, block);
        Ok(())
    }

    fn after_stmt(
        &self,
        cx: &MirPrettyFmt<'_>,
        f: &mut fmt::Formatter<'_>,
        stmt: MirStmtIdx,
    ) -> fmt::Result {
        _ = (cx, f, stmt);
        Ok(())
    }
}

impl<'a> MirPrettyFmt<'a> {
    pub const NO_HOOKS: &'static dyn MirPrettyFmtHooks = {
        struct Impl;

        impl MirPrettyFmtHooks for Impl {}

        &Impl
    };

    pub fn new(tcx: &'a TyCtxt, body: &'a MirBody) -> Self {
        Self {
            tcx,
            body,
            hooks: Self::NO_HOOKS,
        }
    }

    pub fn tcx(&self) -> &'a TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'a Session {
        &self.tcx.session
    }

    pub fn with_hooks<'b>(self, hooks: &'b dyn MirPrettyFmtHooks) -> MirPrettyFmt<'b>
    where
        'a: 'b,
    {
        MirPrettyFmt {
            tcx: self.tcx,
            body: self.body,
            hooks,
        }
    }

    pub fn body(&self) -> &'a MirBody {
        self.body
    }

    pub fn plain_block_label(&self, id: MirBlockIdx) -> impl fmt::Display {
        fmt::from_fn(move |f| write!(f, "{id}"))
    }

    pub fn plain_local_name(&self, id: MirLocalIdx) -> impl fmt::Display {
        fmt::from_fn(move |f| write!(f, "_{}", id.index()))
    }

    pub fn place(&self, place: MirPlace) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            let s = self.session();

            self.plain_local_name(place.local).fmt(f)?;

            for elem in place.projections.r(s) {
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
        })
    }

    pub fn operand(&self, operand: MirOperand) -> impl fmt::Display {
        fmt::from_fn(move |f| match operand {
            MirOperand::Copy(place) => write!(f, "copy({})", self.place(place)),
            MirOperand::Move(place) => write!(f, "move({})", self.place(place)),
        })
    }

    pub fn rvalue(&self, rvalue: &MirRvalue) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            let s = self.session();

            match rvalue {
                MirRvalue::UnreachablePlaceholder => {
                    write!(f, "unreachable")?;
                }
                MirRvalue::Tuple(operands) => {
                    if let [unique] = **operands {
                        write!(f, "({},)", self.operand(unique))?;
                    } else {
                        write!(
                            f,
                            "({})",
                            format_list(
                                operands.iter().map(|&op| self.operand(op)),
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
                                operands.iter().map(|&op| self.operand(op)),
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
                                        self.operand(op)
                                    )
                                }),
                                SimpleListFormatGlue::COMMA_LIST
                            )
                        )?;
                    }
                },
                MirRvalue::Use(operand) => {
                    write!(f, "use({})", self.operand(*operand))?;
                }
                MirRvalue::MoveOutRef {
                    can_move_from,
                    ref_place,
                } => {
                    write!(
                        f,
                        "late-move(*{}, possibly [{}])",
                        self.place(*ref_place),
                        format_list(
                            can_move_from.iter().map(|&place| self.place(place)),
                            SimpleListFormatGlue::COMMA_LIST
                        )
                    )?;
                }
                MirRvalue::Ref(muta, place) => {
                    write!(f, "&{}{}", muta.opt_space_qual(), self.place(*place))?;
                }
                MirRvalue::Zst(ty) => {
                    write!(f, "zst({})", self.ty(*ty))?;
                }
                MirRvalue::Literal(ty, lit) => {
                    write!(f, "{} :: {}", self.lit(*lit), self.ty(*ty))?;
                }
                MirRvalue::BinaryOp(kind, operands) => {
                    write!(
                        f,
                        "{} {} {}",
                        self.operand(operands.0),
                        kind.to_ast().punct().bare_name(),
                        self.operand(operands.1)
                    )?;
                }
                MirRvalue::UnaryOp(kind, operand) => {
                    write!(
                        f,
                        "{}{}",
                        kind.to_ast().punct().bare_name(),
                        self.operand(*operand)
                    )?;
                }
                MirRvalue::Discriminant(place) => {
                    write!(f, "discriminant({})", self.place(*place))?;
                }
                MirRvalue::DynUse(_site, operand) => {
                    write!(f, "dyn-use({})", self.operand(*operand))?;
                }
                MirRvalue::Error(_) => {
                    write!(f, "error")?;
                }
            }

            Ok(())
        })
    }

    pub fn ty(&self, ty: SigTy) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            // TODO
            f.write_str("<type>")
        })
    }

    pub fn lit(&self, lit: AstLit) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            // TODO
            write!(f, "{:?}", lit)
        })
    }

    pub fn plain_stmt(&self, stmt: &MirStmt) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            write!(
                f,
                "{}{}",
                self.plain_stmt_kind(&stmt.kind),
                self.source_info_comment(stmt.source_info)
            )
        })
    }

    pub fn plain_stmt_kind(&self, stmt: &MirStmtKind) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            match &stmt {
                MirStmtKind::StorageLive(local) => {
                    write!(f, "storage-live({});", self.plain_local_name(*local))?;
                }
                MirStmtKind::StorageDead(local) => {
                    write!(f, "storage-dead({});", self.plain_local_name(*local))?;
                }
                MirStmtKind::Assign(stmt) => {
                    write!(f, "{} = {};", self.place(stmt.0), self.rvalue(&stmt.1))?;
                }
                MirStmtKind::Discard(stmt) => {
                    write!(
                        f,
                        "discard({} :: {});",
                        self.rvalue(&stmt.1),
                        self.ty(stmt.0),
                    )?;
                }
            }

            Ok(())
        })
    }

    pub fn plain_terminator(&self, terminator: &MirTerminator) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            write!(
                f,
                "{}{}",
                self.plain_terminator_kind(&terminator.kind),
                self.source_info_comment(terminator.source_info)
            )
        })
    }

    pub fn plain_terminator_kind(&self, terminator: &MirTerminatorKind) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            match terminator {
                MirTerminatorKind::Goto(block) => {
                    write!(f, "goto({});", self.plain_block_label(*block))?;
                }
                MirTerminatorKind::SwitchInt {
                    discr,
                    constants,
                    targets,
                } => {
                    write!(
                        f,
                        "switch({}, [{}]);",
                        self.operand(*discr),
                        format_list(
                            constants.iter().zip(targets).map(|(cst, target)| format!(
                                "{cst} => {}",
                                self.plain_block_label(*target)
                            )),
                            SimpleListFormatGlue::COMMA_LIST
                        )
                    )?;
                }
                MirTerminatorKind::Call {
                    callee,
                    args,
                    destination,
                    target,
                    unwind,
                } => {
                    write!(
                        f,
                        "{} = call({}, [{}]) goto {} unwind {};",
                        self.place(*destination),
                        self.operand(*callee),
                        format_list(
                            args.iter().map(|arg| self.operand(*arg)),
                            SimpleListFormatGlue::COMMA_LIST,
                        ),
                        self.plain_block_label(*target),
                        self.plain_unwind_label(*unwind),
                    )?;
                }
                MirTerminatorKind::EnsureDropped {
                    place,
                    target,
                    unwind,
                } => {
                    write!(
                        f,
                        "ensure-dropped({}) goto {} unwind {};",
                        self.place(*place),
                        self.plain_block_label(*target),
                        self.plain_unwind_label(*unwind),
                    )?;
                }
                MirTerminatorKind::Unreachable => {
                    write!(f, "unreachable;")?;
                }
                MirTerminatorKind::Return => {
                    write!(f, "return;")?;
                }
                MirTerminatorKind::UnwindResume => {
                    write!(f, "unwind-resume;")?;
                }
            }

            Ok(())
        })
    }

    pub fn plain_unwind_label(&self, behavior: MirUnwindBehavior) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            match behavior {
                MirUnwindBehavior::Continue(bb) => {
                    write!(f, "{}", self.plain_block_label(bb))?;
                }
                MirUnwindBehavior::DoublePanic => {
                    f.write_str("<double panic>")?;
                }
            }

            Ok(())
        })
    }

    pub fn source_info_comment(&self, info: MirSourceInfo) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            // TODO
            write!(f, " // {:?}", info)
        })
    }

    pub fn typed_local_name(&self, local: MirLocalIdx) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            write!(
                f,
                "{}: {}",
                self.plain_local_name(local),
                self.ty(self.body.locals[local].ty)
            )
        })
    }

    pub fn flat_body(&self) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            let body = self.body();

            let mut f = IndentedFmt::new(f);

            writeln!(
                f,
                "fn({}) -> {} {{",
                format_list(
                    body.locals
                        .indices()
                        .skip(1)
                        .take(body.arg_count as usize)
                        .map(|local| self.typed_local_name(local)),
                    SimpleListFormatGlue::COMMA_LIST,
                ),
                self.typed_local_name(MirLocalIdx::RETURN),
            )?;

            f.change_level_now(4)?;

            let mut had_local = false;

            for local in body.locals.indices().skip(body.arg_count as usize + 1) {
                writeln!(f, "let {};", self.typed_local_name(local))?;
                had_local = true;
            }

            if had_local {
                writeln!(f)?;
            }

            for block in body.blocks() {
                f.change_level_now(-4)?;
                writeln!(
                    f,
                    "{}{}:",
                    if block.block == body.entry {
                        "[entry] "
                    } else {
                        ""
                    },
                    self.plain_block_label(block.block)
                )?;
                f.change_level_now(4)?;

                fmt_write(&mut f, |f| self.hooks.start_of_block(self, f, block.block))?;

                for stmt in block.stmts(MirBodyDirection::Forwards) {
                    writeln!(f, "{}", self.plain_stmt(stmt.stmt()))?;

                    fmt_write(&mut f, |f| self.hooks.after_stmt(self, f, stmt.stmt))?;
                }

                if let Some(terminator) = block.opt_terminator() {
                    writeln!(f, "{}\n", self.plain_terminator(terminator))?;
                } else {
                    writeln!(f, "<missing terminator>\n")?;
                }
            }

            f.change_level_now(-4)?;

            writeln!(f, "}}")?;

            Ok(())
        })
    }
}
