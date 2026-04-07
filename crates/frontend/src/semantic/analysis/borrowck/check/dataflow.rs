use crate::{
    base::Session,
    semantic::{
        analysis::TyCtxt,
        syntax::{
            MirAssignRvalue, MirBlock, MirBlockIdx, MirBody, MirDirection, MirInstructionIdx,
            MirInstructionLoc, MirInstructionRef, MirLocalIdx, MirOperand, MirPlace, MirStmt,
            MirStmtKind, MirTerminator,
        },
    },
};
use index_vec::IndexVec;
use rustc_hash::FxHashSet;
use smallvec::SmallVec;
use std::{
    collections::VecDeque,
    convert::Infallible,
    fmt, iter, mem,
    ops::{ControlFlow, RangeBounds},
};

// === MirBbOperation === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct MirBbOperation {
    pub kind: MirBbOperationKind,
    pub place: MirLocalIdx,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MirBbOperationKind {
    Provide,
    Steal,
    Use,
}

pub struct MirBbOperationVisitor<'a, F, B>(pub &'a Session, pub F)
where
    F: FnMut(MirBbOperation) -> ControlFlow<B>;

impl<F, B> MirBbOperationVisitor<'_, F, B>
where
    F: FnMut(MirBbOperation) -> ControlFlow<B>,
{
    pub fn visit_instr(&mut self, instr: MirInstructionRef<'_>) -> ControlFlow<B> {
        match instr {
            MirInstructionRef::Stmt(stmt) => self.visit_stmt(stmt),
            MirInstructionRef::Terminator(terminator) => self.visit_terminator(terminator),
        }
    }

    pub fn visit_stmt(&mut self, stmt: &MirStmt) -> ControlFlow<B> {
        match &stmt.kind {
            MirStmtKind::Assign(stmt) => {
                let (lhs, rhs) = &**stmt;
                self.visit_rvalue(rhs)?;
                self.visit_place(MirBbOperationKind::Provide, *lhs)?;
            }
            MirStmtKind::Discard(operand) => {
                self.visit_operand(*operand)?;
            }
        }

        ControlFlow::Continue(())
    }

    pub fn visit_terminator(&mut self, terminator: &MirTerminator) -> ControlFlow<B> {
        match terminator {
            MirTerminator::Call {
                callee,
                args,
                destination,
                target: _,
            } => {
                self.visit_operand(*callee)?;
                self.visit_operand_list(args)?;
                self.visit_place(MirBbOperationKind::Provide, *destination)?;
            }
            MirTerminator::Drop { place, target: _ } => {
                self.visit_place(MirBbOperationKind::Steal, *place)?;
            }
            MirTerminator::Switch {
                scrutinee,
                targets: _,
            } => {
                self.visit_place(MirBbOperationKind::Use, *scrutinee)?;
            }
            MirTerminator::Goto(_)
            | MirTerminator::Return
            | MirTerminator::Unreachable
            | MirTerminator::Placeholder => {
                // (empty)
            }
        }

        ControlFlow::Continue(())
    }

    pub fn visit_rvalue(&mut self, rvalue: &MirAssignRvalue) -> ControlFlow<B> {
        match rvalue {
            MirAssignRvalue::Tuple(elems) => {
                self.visit_operand_list(elems)?;
            }
            MirAssignRvalue::Use(operand) => {
                self.visit_operand(*operand)?;
            }
            MirAssignRvalue::Ref(_muta, place) => {
                self.visit_place(MirBbOperationKind::Use, *place)?;
            }
            MirAssignRvalue::Zst(_) | MirAssignRvalue::Literal(_, _) => {
                // (empty)
            }
            MirAssignRvalue::BinaryOp(_kind, operands) => {
                let (lhs, rhs) = &**operands;
                self.visit_operand(*lhs)?;
                self.visit_operand(*rhs)?;
            }
            MirAssignRvalue::UnaryOp(_kind, operand) => {
                self.visit_operand(*operand)?;
            }
            MirAssignRvalue::Discriminant(place) => {
                self.visit_place(MirBbOperationKind::Use, *place)?;
            }
        }

        ControlFlow::Continue(())
    }

    pub fn visit_operand_list(&mut self, operands: &[MirOperand]) -> ControlFlow<B> {
        for &operand in operands {
            self.visit_operand(operand)?;
        }

        ControlFlow::Continue(())
    }

    pub fn visit_operand(&mut self, operand: MirOperand) -> ControlFlow<B> {
        match operand {
            MirOperand::Copy(place) => self.visit_place(MirBbOperationKind::Use, place),
            MirOperand::Move(place) => self.visit_place(MirBbOperationKind::Steal, place),
        }
    }

    pub fn visit_place(&mut self, kind: MirBbOperationKind, place: MirPlace) -> ControlFlow<B> {
        // TODO
        if !place.projections.r(self.0).is_empty() {
            return ControlFlow::Continue(());
        }

        (self.1)(MirBbOperation {
            kind,
            place: place.local,
        })
    }
}

// === MirDataflowFacts === //

pub struct MirDataflowFacts {
    pub occupancy: MirDataflow,
    pub liveness: MirDataflow,
}

impl MirDataflowFacts {
    pub fn compute(tcx: &TyCtxt, body: &MirBody) -> Self {
        let s = &tcx.session;

        // Compute occupancy
        let occupancy = MirDataflow::new(
            body,
            LocalSetJoinOp::Intersect,
            MirDirection::Forward,
            |loc| {
                let mut gk = GenKillTrans::new(body.locals.len());
                MirBbOperationVisitor(s, |op| {
                    match op.kind {
                        MirBbOperationKind::Provide => {
                            gk.push_gen(op.place);
                        }
                        MirBbOperationKind::Steal => {
                            gk.push_kill(op.place);
                        }
                        MirBbOperationKind::Use => {
                            // (no effect)
                        }
                    }

                    ControlFlow::<Infallible>::Continue(())
                })
                .visit_instr(body.lookup(loc));
                gk
            },
        );

        // Compute liveness
        let liveness =
            MirDataflow::new(body, LocalSetJoinOp::Union, MirDirection::Backward, |loc| {
                let mut gk = GenKillTrans::new(body.locals.len());
                MirBbOperationVisitor(s, |op| {
                    match op.kind {
                        MirBbOperationKind::Provide => {
                            gk.push_kill(op.place);
                        }
                        MirBbOperationKind::Use | MirBbOperationKind::Steal => {
                            gk.push_gen(op.place);
                        }
                    }

                    ControlFlow::<Infallible>::Continue(())
                })
                .visit_instr(body.lookup(loc));
                gk
            });

        Self {
            occupancy,
            liveness,
        }
    }

    pub fn find_last_thief(
        &self,
        s: &Session,
        body: &MirBody,
        location: MirInstructionLoc,
        place: MirLocalIdx,
    ) -> Option<MirInstructionLoc> {
        fn find_local_thief(
            s: &Session,
            block: &MirBlock,
            range: impl RangeBounds<MirInstructionIdx>,
            place: MirLocalIdx,
        ) -> Option<MirInstructionIdx> {
            block.instructions_ranged(range).rev().find(|&idx| {
                MirBbOperationVisitor(s, |op| {
                    if op.kind == MirBbOperationKind::Steal && op.place == place {
                        ControlFlow::Break(())
                    } else {
                        ControlFlow::Continue(())
                    }
                })
                .visit_instr(block.lookup(idx))
                .is_break()
            })
        }

        if let Some(thief) =
            find_local_thief(s, &body.blocks[location.block], ..location.instr, place)
        {
            return Some(MirInstructionLoc {
                block: location.block,
                instr: thief,
            });
        }

        let mut dfs_set = FxHashSet::default();
        let mut dfs_stack = Vec::new();
        let mut candidates = Vec::new();

        for &pred in body.blocks[location.block].predecessors() {
            if !dfs_set.insert(pred) {
                continue;
            }

            dfs_stack.push(pred);
        }

        while let Some(curr) = dfs_stack.pop() {
            if let Some(thief) = find_local_thief(s, &body.blocks[curr], .., place) {
                candidates.push(MirInstructionLoc {
                    block: curr,
                    instr: thief,
                });

                continue;
            }

            for &pred in body.blocks[curr].predecessors() {
                if !dfs_set.insert(pred) {
                    continue;
                }

                dfs_stack.push(pred);
            }
        }

        candidates
            .into_iter()
            .max_by_key(|&instr| body.lookup(instr).span().hi)
    }

    pub fn find_next_use(&self) {
        todo!()
    }

    #[must_use]
    pub fn can_outlive_rhs_mask(&self, body: &MirBody, rhs: MirLocalIdx) -> LocalSet {
        // `lhs` is allowed to outlive `rhs` if, for every instruction, `live(rhs)` implies
        // `occupied(lhs)`. In other words, a local is allowed to outlive another one if, whenever
        // the `rhs` local is in use, `lhs` can be referred to.
        //
        // Here is a pair of examples to help demonstrate this idea.
        //
        // This program is accepted:
        //
        // ```
        // // occupied: {}, live: {}
        // let mut a = Vec::<i32>::new();
        // // occupied: {a}, live: {a}
        // let mut b: &'_ mut Vec<i32> = &mut a;
        // // occupied: {a, b}, live: {a, b}
        // b.clear();
        // // occupied: {a, b}, live: {a}
        // drop(a);
        // // occupied: {b}, live: {}
        // a = Vec::<i32>::new();
        // // occupied: {a, b}, live: {a}
        // b = &mut a;
        // // occupied: {a, b}, live: {b}
        // b.clear();
        // // occupied: {a, b}, live: {}
        //
        // // 'a can outlive 'b iff, for all instructions, live(b) implies occupied(a)
        // // This is satisfied by this code so it compiles!
        // ```
        //
        // ...while this program is rejected:
        //
        // ```
        // // occupied: {}, live: {}
        // let mut a = Vec::<i32>::new();
        // // occupied: {a}, live: {a}
        // let mut b: &'_ mut Vec<i32> = &mut a;
        // // occupied: {a, b}, live: {a, b}
        // b.clear();
        // // occupied: {a, b}, live: {a, b}
        // drop(a);
        // // occupied: {b}, live: {b}
        // a = Vec::<i32>::new();
        // // occupied: {a, b}, live: {a, b}
        // b.clear();
        // // occupied: {a, b}, live: {a, b}
        // b = &mut a;
        // // occupied: {a, b}, live: {b}
        // b.clear();
        // // occupied: {a, b}, live: {}
        //
        // // 'a can outlive 'b iff, for all instructions, live(b) implies occupied(a)
        // // This is broken by...
        // //
        // // ```
        // // drop(a);
        // // // occupied: {b}, live: {b}
        // // ```
        // //
        // // ...so the code fails to compile!
        // ```

        let mut outlive_mask = LocalSet::new(body.locals.len());
        outlive_mask.fill();

        let mut push = |occupancy: &LocalSet, liveness: &LocalSet| {
            if !liveness.contains(rhs) {
                return;
            }

            outlive_mask.intersect(occupancy);
        };

        for (block_idx, block) in body.blocks.iter_enumerated() {
            for instr_idx in block.instructions() {
                let loc = MirInstructionLoc {
                    block: block_idx,
                    instr: instr_idx,
                };

                push(
                    self.occupancy.state_before(loc),
                    self.liveness.state_before(loc),
                );
            }

            let loc = MirInstructionLoc {
                block: block_idx,
                instr: block.terminator_idx(),
            };

            push(
                self.occupancy.state_after(loc),
                self.liveness.state_after(loc),
            );
        }

        outlive_mask
    }
}

// === MirDataflow === //

#[derive(Clone)]
pub struct MirDataflow {
    results: IndexVec<MirBlockIdx, Vec<LocalSet>>,
}

impl MirDataflow {
    pub fn new(
        body: &MirBody,
        join_op: LocalSetJoinOp,
        direction: MirDirection,
        mut trans: impl FnMut(MirInstructionLoc) -> GenKillTrans,
    ) -> Self {
        struct Solver<'a> {
            body: &'a MirBody,
            join_op: LocalSetJoinOp,
            direction: MirDirection,
            block_scratch: IndexVec<MirBlockIdx, BlockScratch>,
            work_queue: VecDeque<MirBlockIdx>,
        }

        struct BlockScratch {
            natural_gen_kill: Vec<GenKillTrans>,
            natural_total_trans: GenKillTrans,
            results: LocalSet,
            in_work_list: bool,
        }

        impl Solver<'_> {
            fn update_to_fixpoint(&mut self) {
                let mut tmp_set = LocalSet::new(self.body.locals.len());

                for bb in self.block_scratch.indices() {
                    self.mark_dirty(bb);
                }

                while let Some(curr) = self.work_queue.pop_front() {
                    self.block_scratch[curr].in_work_list = false;

                    // Join predecessors
                    self.import_start(curr, &mut tmp_set);

                    // Transition through the block.
                    tmp_set.trans(&self.block_scratch[curr].natural_total_trans);

                    // If our set changed, mark the successors as dirty.
                    if tmp_set == self.block_scratch[curr].results {
                        continue;
                    }

                    self.block_scratch[curr].results.clone_from(&tmp_set);

                    for &succ in self.body.blocks[curr].next(self.direction) {
                        self.mark_dirty(succ);
                    }
                }
            }

            fn import_start(&self, curr: MirBlockIdx, target: &mut LocalSet) {
                if let Some((first, remaining)) =
                    self.body.blocks[curr].prev(self.direction).split_first()
                {
                    target.clone_from(&self.block_scratch[*first].results);

                    for &flow_from in remaining {
                        target.join(self.join_op, &self.block_scratch[flow_from].results);
                    }
                } else {
                    target.clear();
                }
            }

            fn mark_dirty(&mut self, bb: MirBlockIdx) {
                if mem::replace(&mut self.block_scratch[bb].in_work_list, true) {
                    return;
                }

                self.work_queue.push_back(bb);
            }
        }

        let block_tmp = body
            .blocks
            .iter_enumerated()
            .map(|(block_idx, block)| {
                let mut natural_gen_kill = block
                    .instructions()
                    .map(|instr_idx| {
                        trans(MirInstructionLoc {
                            block: block_idx,
                            instr: instr_idx,
                        })
                    })
                    .collect::<Vec<_>>();

                if direction.is_backward() {
                    natural_gen_kill.reverse();
                }

                let mut natural_total_trans = GenKillTrans::new(body.locals.len());

                for step in &natural_gen_kill {
                    natural_total_trans.push_all(step);
                }

                BlockScratch {
                    natural_gen_kill,
                    natural_total_trans,
                    results: LocalSet::new(body.locals.len()),
                    in_work_list: false,
                }
            })
            .collect();

        let mut solver = Solver {
            body,
            join_op,
            direction,
            block_scratch: block_tmp,
            work_queue: VecDeque::new(),
        };
        solver.update_to_fixpoint();

        let results = solver
            .block_scratch
            .iter_enumerated()
            .map(|(block_idx, block_scratch)| {
                let mut points = Vec::new();
                let mut next_point = LocalSet::new(body.locals.len());

                // Create the entry-point state.
                solver.import_start(block_idx, &mut next_point);
                points.push(next_point.clone());

                // Create all intermediate states.
                for trans in &block_scratch.natural_gen_kill {
                    next_point.trans(trans);
                    points.push(next_point.clone());
                }

                debug_assert_eq!(points.last().unwrap(), &block_scratch.results);

                // Reorder into forward direction
                if direction.is_backward() {
                    points.reverse();
                }

                points
            })
            .collect::<IndexVec<MirBlockIdx, _>>();

        Self { results }
    }

    pub fn state_before(&self, location: MirInstructionLoc) -> &LocalSet {
        &self.results[location.block][location.instr.0]
    }

    pub fn state_after(&self, location: MirInstructionLoc) -> &LocalSet {
        &self.results[location.block][location.instr.0 + 1]
    }
}

// === LocalSet === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum LocalSetJoinOp {
    Union,
    Intersect,
}

#[derive(Eq, PartialEq)]
pub struct GenKillTrans {
    gen_set: LocalSet,
    kill_set: LocalSet,
}

impl GenKillTrans {
    pub fn new(local_count: usize) -> Self {
        Self {
            gen_set: LocalSet::new(local_count),
            kill_set: LocalSet::new(local_count),
        }
    }

    pub fn push_gen(&mut self, idx: MirLocalIdx) {
        self.gen_set.add(idx);
        self.kill_set.remove(idx);
    }

    pub fn push_kill(&mut self, idx: MirLocalIdx) {
        self.kill_set.add(idx);
        self.gen_set.remove(idx);
    }

    pub fn push_all(&mut self, other: &GenKillTrans) {
        self.gen_set.union(&other.gen_set);
        self.kill_set.remove_all(&other.gen_set);

        self.gen_set.remove_all(&other.kill_set);
        self.kill_set.union(&other.kill_set);
    }

    pub fn gen_set(&self) -> &LocalSet {
        &self.gen_set
    }

    pub fn kill_set(&self) -> &LocalSet {
        &self.kill_set
    }
}

#[derive(Eq, PartialEq)]
pub struct LocalSet {
    set: SmallVec<[u64; 1]>,
    len: usize,
}

impl fmt::Debug for LocalSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl Clone for LocalSet {
    fn clone(&self) -> Self {
        Self {
            set: self.set.clone(),
            len: self.len,
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.set.clone_from(&source.set);
        self.len = source.len;
    }
}

impl LocalSet {
    pub fn new(local_count: usize) -> Self {
        Self {
            set: (0..local_count.div_ceil(64)).map(|_| 0u64).collect(),
            len: local_count,
        }
    }

    pub fn add(&mut self, idx: MirLocalIdx) {
        self.set[idx.index() / 64] |= 1 << (idx.index() % 64);
    }

    pub fn remove(&mut self, idx: MirLocalIdx) {
        self.set[idx.index() / 64] &= !(1 << (idx.index() % 64));
    }

    pub fn trans(&mut self, trans: &GenKillTrans) {
        self.union(&trans.gen_set);
        self.remove_all(&trans.kill_set);
    }

    pub fn fill(&mut self) {
        for v in &mut self.set {
            *v = u64::MAX;
        }

        if let Some(last) = self.set.last_mut() {
            *last = (1 << (self.len % 64)) - 1;
        }
    }

    pub fn clear(&mut self) {
        for v in &mut self.set {
            *v = 0u64;
        }
    }

    #[must_use]
    pub fn contains(&self, idx: MirLocalIdx) -> bool {
        self.set[idx.index() / 64] & 1 << (idx.index() % 64) != 0
    }

    pub fn join(&mut self, op: LocalSetJoinOp, other: &LocalSet) {
        match op {
            LocalSetJoinOp::Union => self.union(other),
            LocalSetJoinOp::Intersect => self.intersect(other),
        }
    }

    pub fn union(&mut self, other: &LocalSet) {
        for (lhs, rhs) in self.set.iter_mut().zip(&other.set) {
            *lhs |= *rhs;
        }
    }

    pub fn intersect(&mut self, other: &LocalSet) {
        for (lhs, rhs) in self.set.iter_mut().zip(&other.set) {
            *lhs &= *rhs;
        }
    }

    pub fn remove_all(&mut self, other: &LocalSet) {
        for (lhs, rhs) in self.set.iter_mut().zip(&other.set) {
            *lhs &= !*rhs;
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = MirLocalIdx> {
        let mut next_word_idx = 1usize;
        let mut curr_word_val = self.set.first().copied().unwrap_or(0);

        iter::from_fn(move || {
            loop {
                if curr_word_val != 0 {
                    let idx = curr_word_val.trailing_zeros() as usize;
                    curr_word_val ^= 1 << idx;
                    return Some(MirLocalIdx::from_usize((next_word_idx - 1) * 64 + idx));
                }

                let &next_word = self.set.get(next_word_idx)?;
                curr_word_val = next_word;
                next_word_idx += 1;
            }
        })
    }
}
