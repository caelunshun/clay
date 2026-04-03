use crate::{
    base::Session,
    semantic::{
        analysis::TyCtxt,
        syntax::{
            MirAssignRvalue, MirBlock, MirBlockIdx, MirBody, MirLocalIdx, MirOperand, MirPlace,
            MirStmt, MirStmtKind, MirTerminator,
        },
    },
};
use index_vec::IndexVec;
use smallvec::SmallVec;
use std::{collections::VecDeque, fmt, iter, mem};

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

pub fn mir_block_operations(bb: &MirBlock, s: &Session) -> SmallVec<[MirBbOperation; 2]> {
    struct Collector<'a> {
        collector: SmallVec<[MirBbOperation; 2]>,
        s: &'a Session,
    }

    impl Collector<'_> {
        fn visit_block(&mut self, bb: &MirBlock) {
            for stmt in &bb.stmts {
                self.visit_stmt(stmt);
            }

            self.visit_terminator(&bb.terminator);
        }

        fn visit_stmt(&mut self, stmt: &MirStmt) {
            match &stmt.kind {
                MirStmtKind::Assign(stmt) => {
                    let (lhs, rhs) = &**stmt;
                    self.visit_rvalue(rhs);
                    self.visit_place(MirBbOperationKind::Provide, *lhs);
                }
                MirStmtKind::Discard(operand) => {
                    self.visit_operand(*operand);
                }
            }
        }

        fn visit_terminator(&mut self, terminator: &MirTerminator) {
            match terminator {
                MirTerminator::Call {
                    callee,
                    args,
                    destination,
                    target: _,
                } => {
                    self.visit_operand(*callee);
                    self.visit_operand_list(args);
                    self.visit_place(MirBbOperationKind::Provide, *destination);
                }
                MirTerminator::Drop { place, target: _ } => {
                    self.visit_place(MirBbOperationKind::Steal, *place);
                }
                MirTerminator::Switch {
                    scrutinee,
                    targets: _,
                } => {
                    self.visit_place(MirBbOperationKind::Use, *scrutinee);
                }
                MirTerminator::Goto(_)
                | MirTerminator::Return
                | MirTerminator::Unreachable
                | MirTerminator::Placeholder => {
                    // (empty)
                }
            }
        }

        fn visit_rvalue(&mut self, rvalue: &MirAssignRvalue) {
            match rvalue {
                MirAssignRvalue::Tuple(elems) => {
                    self.visit_operand_list(elems);
                }
                MirAssignRvalue::Use(operand) => {
                    self.visit_operand(*operand);
                }
                MirAssignRvalue::Ref(_muta, place) => {
                    self.visit_place(MirBbOperationKind::Use, *place);
                }
                MirAssignRvalue::Zst | MirAssignRvalue::Literal(_) => {
                    // (empty)
                }
                MirAssignRvalue::BinaryOp(_kind, operands) => {
                    let (lhs, rhs) = &**operands;
                    self.visit_operand(*lhs);
                    self.visit_operand(*rhs);
                }
                MirAssignRvalue::UnaryOp(_kind, operand) => {
                    self.visit_operand(*operand);
                }
                MirAssignRvalue::Discriminant(place) => {
                    self.visit_place(MirBbOperationKind::Use, *place);
                }
            }
        }

        fn visit_operand_list(&mut self, operands: &[MirOperand]) {
            for &operand in operands {
                self.visit_operand(operand);
            }
        }

        fn visit_operand(&mut self, operand: MirOperand) {
            match operand {
                MirOperand::Copy(place) => self.visit_place(MirBbOperationKind::Use, place),
                MirOperand::Move(place) => self.visit_place(MirBbOperationKind::Steal, place),
            }
        }

        fn visit_place(&mut self, kind: MirBbOperationKind, place: MirPlace) {
            // TODO
            if !place.projections.r(self.s).is_empty() {
                return;
            }

            self.collector.push(MirBbOperation {
                kind,
                place: place.local,
            });
        }
    }

    let mut collector = Collector {
        collector: SmallVec::new(),
        s,
    };
    collector.visit_block(bb);
    collector.collector
}

// === MirDataflowFacts === //

#[derive(Debug, Clone)]
pub struct MirDataflowFacts {
    pub occupied: IndexVec<MirBlockIdx, LocalSet>,
    pub live: IndexVec<MirBlockIdx, LocalSet>,
}

impl MirDataflowFacts {
    pub fn compute(tcx: &TyCtxt, body: &MirBody) -> Self {
        let s = &tcx.session;

        // Compute occupancy
        let occupied = {
            let mut df = DataflowBuilder::new(
                DataflowJoinOp::Intersect,
                body.blocks.len(),
                body.locals.len(),
            );

            for (curr, curr_state) in body.blocks.iter_enumerated() {
                for &succ in curr_state.terminator.successors() {
                    df.add_successor(curr, succ);
                }

                dbg!(curr);

                for op in dbg!(mir_block_operations(curr_state, s)) {
                    match op.kind {
                        MirBbOperationKind::Provide => {
                            df.add_gen(curr, op.place);
                        }
                        MirBbOperationKind::Steal => {
                            df.add_kill(curr, op.place);
                        }
                        MirBbOperationKind::Use => {
                            // (ignored)
                        }
                    }
                }

                dbg!(&curr_state.terminator);
            }

            df.compute()
        };

        // Compute liveness
        let live = {
            let mut df =
                DataflowBuilder::new(DataflowJoinOp::Union, body.blocks.len(), body.locals.len());

            for (curr, curr_state) in body.blocks.iter_enumerated() {
                for &succ in curr_state.terminator.successors() {
                    df.add_successor(succ, curr);
                }

                for &op in mir_block_operations(curr_state, s).iter().rev() {
                    match op.kind {
                        MirBbOperationKind::Provide => {
                            df.add_kill(curr, op.place);
                        }
                        MirBbOperationKind::Steal | MirBbOperationKind::Use => {
                            df.add_gen(curr, op.place);
                        }
                    }
                }
            }

            df.compute()
        };

        Self { occupied, live }
    }

    pub fn find_last_thief(&self) {
        todo!()
    }

    pub fn find_next_use(&self) {
        todo!()
    }

    #[must_use]
    pub fn can_outlive(&self, lhs: MirLocalIdx, rhs: MirLocalIdx) -> bool {
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

        todo!()
    }
}

// === DataflowBuilder === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum DataflowJoinOp {
    Union,
    Intersect,
}

pub struct DataflowBuilder {
    join_op: DataflowJoinOp,
    blocks: IndexVec<MirBlockIdx, DataflowBlock>,
    local_count: usize,
}

struct DataflowBlock {
    gen_set: LocalSet,
    kill_set: LocalSet,
    flow_from: Vec<MirBlockIdx>,
    flow_into: Vec<MirBlockIdx>,
    in_work_list: bool,
}

impl DataflowBuilder {
    pub fn new(join_op: DataflowJoinOp, bb_count: usize, local_count: usize) -> Self {
        Self {
            join_op,
            blocks: IndexVec::from_iter((0..bb_count).map(|_| DataflowBlock {
                gen_set: LocalSet::new(local_count),
                kill_set: LocalSet::new(local_count),
                flow_from: Vec::new(),
                flow_into: Vec::new(),
                in_work_list: false,
            })),
            local_count,
        }
    }

    pub fn add_successor(&mut self, src: MirBlockIdx, dst: MirBlockIdx) {
        self.blocks[src].flow_into.push(dst);
        self.blocks[dst].flow_from.push(src);
    }

    pub fn add_gen(&mut self, bb: MirBlockIdx, local: MirLocalIdx) {
        let bb = &mut self.blocks[bb];
        bb.gen_set.add(local);
        bb.kill_set.remove(local);
    }

    pub fn add_kill(&mut self, bb: MirBlockIdx, local: MirLocalIdx) {
        let bb = &mut self.blocks[bb];
        bb.kill_set.add(local);
        bb.gen_set.remove(local);
    }

    #[must_use]
    pub fn compute(self) -> IndexVec<MirBlockIdx, LocalSet> {
        struct Worker {
            dataflow: DataflowBuilder,
            block_outputs: IndexVec<MirBlockIdx, LocalSet>,
            work_queue: VecDeque<MirBlockIdx>,
            tmp_set: LocalSet,
        }

        impl Worker {
            fn update_to_fixpoint(&mut self) {
                for bb in self.block_outputs.indices() {
                    self.mark_dirty(bb);
                }

                while let Some(curr) = self.work_queue.pop_front() {
                    self.dataflow.blocks[curr].in_work_list = false;

                    // Join predecessors
                    if let Some((first, remaining)) =
                        self.dataflow.blocks[curr].flow_from.split_first()
                    {
                        self.tmp_set.clone_from(&self.block_outputs[*first]);

                        for &flow_from in remaining {
                            self.tmp_set
                                .join(self.dataflow.join_op, &self.block_outputs[flow_from]);
                        }
                    } else {
                        self.tmp_set.clear();
                    }

                    // Transition through the block.
                    self.tmp_set.union(&self.dataflow.blocks[curr].gen_set);
                    self.tmp_set
                        .remove_all(&self.dataflow.blocks[curr].kill_set);

                    // If our set changed, mark the successors as dirty.
                    if self.tmp_set == self.block_outputs[curr] {
                        continue;
                    }

                    self.block_outputs[curr].clone_from(&self.tmp_set);

                    for succ_idx in 0..self.dataflow.blocks[curr].flow_into.len() {
                        self.mark_dirty(self.dataflow.blocks[curr].flow_into[succ_idx]);
                    }
                }
            }

            fn mark_dirty(&mut self, bb: MirBlockIdx) {
                if mem::replace(&mut self.dataflow.blocks[bb].in_work_list, true) {
                    return;
                }

                self.work_queue.push_back(bb);
            }
        }

        let mut worker = Worker {
            block_outputs: self
                .blocks
                .iter()
                .map(|_| LocalSet::new(self.local_count))
                .collect::<IndexVec<MirBlockIdx, LocalSet>>(),
            tmp_set: LocalSet::new(self.local_count),
            work_queue: VecDeque::new(),
            dataflow: self,
        };

        worker.update_to_fixpoint();

        worker.block_outputs
    }
}

// === LocalSet === //

#[derive(Eq, PartialEq)]
pub struct LocalSet {
    set: SmallVec<[u64; 1]>,
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
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.set.clone_from(&source.set);
    }
}

impl LocalSet {
    pub fn new(local_count: usize) -> Self {
        Self {
            set: (0..local_count.div_ceil(64)).map(|_| 0u64).collect(),
        }
    }

    pub fn add(&mut self, idx: MirLocalIdx) {
        self.set[idx.index() / 64] |= 1 << (idx.index() % 64);
    }

    pub fn remove(&mut self, idx: MirLocalIdx) {
        self.set[idx.index() / 64] &= !(1 << (idx.index() % 64));
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

    pub fn join(&mut self, op: DataflowJoinOp, other: &LocalSet) {
        match op {
            DataflowJoinOp::Union => self.union(other),
            DataflowJoinOp::Intersect => self.intersect(other),
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

// === Tests === //

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_dataflow_liveness_1() {
        let mut df = DataflowBuilder::new(DataflowJoinOp::Union, 3, 1);

        df.add_successor(MirBlockIdx::from_usize(0), MirBlockIdx::from_usize(1));
        df.add_successor(MirBlockIdx::from_usize(1), MirBlockIdx::from_usize(2));
        df.add_successor(MirBlockIdx::from_usize(2), MirBlockIdx::from_usize(0));

        df.add_gen(MirBlockIdx::from_usize(0), MirLocalIdx::from_usize(0));
        df.add_kill(MirBlockIdx::from_usize(2), MirLocalIdx::from_usize(0));

        let df = df.compute();

        assert!(df[0].contains(MirLocalIdx::from_usize(0)));
        assert!(df[1].contains(MirLocalIdx::from_usize(0)));
        assert!(!df[2].contains(MirLocalIdx::from_usize(0)));
    }

    #[test]
    fn simple_dataflow_liveness_2() {
        let mut df = DataflowBuilder::new(DataflowJoinOp::Union, 3, 1);

        df.add_successor(MirBlockIdx::from_usize(0), MirBlockIdx::from_usize(1));
        df.add_successor(MirBlockIdx::from_usize(1), MirBlockIdx::from_usize(2));
        df.add_successor(MirBlockIdx::from_usize(2), MirBlockIdx::from_usize(0));

        df.add_gen(MirBlockIdx::from_usize(0), MirLocalIdx::from_usize(0));
        df.add_kill(MirBlockIdx::from_usize(1), MirLocalIdx::from_usize(0));

        let df = df.compute();

        assert!(df[0].contains(MirLocalIdx::from_usize(0)));
        assert!(!df[1].contains(MirLocalIdx::from_usize(0)));
        assert!(!df[2].contains(MirLocalIdx::from_usize(0)));
    }
}
