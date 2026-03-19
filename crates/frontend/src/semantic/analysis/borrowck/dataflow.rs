use crate::{
    base::Session,
    semantic::{
        analysis::TyCtxt,
        syntax::{MirBlock, MirBlockIdx, MirBody, MirLocalIdx},
    },
};
use index_vec::IndexVec;
use smallvec::SmallVec;
use std::{collections::VecDeque, fmt, iter, mem, ops::ControlFlow};

// === Main Calculations === //

#[derive(Debug, Copy, Clone)]
pub enum MirBbOperation {
    Provide(MirLocalIdx),
    Steal(MirLocalIdx),
    Use(MirLocalIdx),
}

pub fn iter_bb_successors<B>(
    bb: &MirBlock,
    s: &Session,
    mut f: impl FnMut(MirBlockIdx) -> ControlFlow<B>,
) -> ControlFlow<B> {
    todo!()
}

pub fn iter_bb_operations<B>(
    bb: &MirBlock,
    s: &Session,
    mut f: impl FnMut(MirBbOperation) -> ControlFlow<B>,
) -> ControlFlow<B> {
    todo!()
}

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
            let mut df = Dataflow::new(
                DataflowJoinOp::Intersect,
                body.blocks.len(),
                body.locals.len(),
            );

            for (curr, curr_state) in body.blocks.iter_enumerated() {
                cbit::cbit!(for succ in iter_bb_successors(curr_state, s) {
                    df.add_successor(curr, succ);
                });

                cbit::cbit!(for op in iter_bb_operations(curr_state, s) {
                    match op {
                        MirBbOperation::Provide(idx) => {
                            df.add_gen(curr, idx);
                        }
                        MirBbOperation::Steal(idx) => {
                            df.add_kill(curr, idx);
                        }
                        MirBbOperation::Use(_) => {
                            // (ignored)
                        }
                    }
                });
            }

            df.compute()
        };

        // Compute liveness
        let live = {
            let mut df = Dataflow::new(DataflowJoinOp::Union, body.blocks.len(), body.locals.len());

            for (curr, curr_state) in body.blocks.iter_enumerated() {
                cbit::cbit!(for succ in iter_bb_successors(curr_state, s) {
                    df.add_successor(succ, curr);
                });

                cbit::cbit!(for op in iter_bb_operations(curr_state, s) {
                    match op {
                        MirBbOperation::Provide(idx) => {
                            df.add_kill(curr, idx);
                        }
                        MirBbOperation::Steal(idx) | MirBbOperation::Use(idx) => {
                            df.add_gen(curr, idx);
                        }
                    }
                });
            }

            df.compute()
        };

        // Detect uses of unoccupied values.
        // TODO

        Self { occupied, live }
    }
}

// === Infrastructure === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum DataflowJoinOp {
    Union,
    Intersect,
}

pub struct Dataflow {
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

impl Dataflow {
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
            dataflow: Dataflow,
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

                    self.tmp_set.clear();

                    for &flow_from in &self.dataflow.blocks[curr].flow_from {
                        self.tmp_set
                            .join(self.dataflow.join_op, &self.block_outputs[flow_from]);
                    }

                    self.tmp_set.union(&self.dataflow.blocks[curr].gen_set);
                    self.tmp_set
                        .remove_all(&self.dataflow.blocks[curr].kill_set);

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
        self.set[idx.index() / 64] ^= !(1 << (idx.index() % 64));
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
        let mut df = Dataflow::new(DataflowJoinOp::Union, 3, 1);

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
        let mut df = Dataflow::new(DataflowJoinOp::Union, 3, 1);

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
