use crate::{
    semantic::syntax::{MirBlockIdx, MirBody, MirBodyDirection, MirStmtIdx},
    utils::mem::{DisjointBorrowsScratch, VecOfPtrScratch},
};
use derive_where::derive_where;
use slotmap::SecondaryMap;
use std::{collections::VecDeque, mem};

// === DataflowAnalysis === //

pub trait ForwardsDataflowAnalysis<'g> {
    type Lattice;

    fn body(&self) -> &'g MirBody;

    fn init_effect(&mut self, is_entry: bool) -> Self::Lattice;

    fn trans_join(&mut self, inputs: &[&Self::Lattice], output: &mut DataflowOutput<Self::Lattice>);

    fn trans_stmt(&mut self, idx: MirStmtIdx, input: &Self::Lattice, output: &mut Self::Lattice);

    fn trans_terminator(
        &mut self,
        idx: MirBlockIdx,
        input: &Self::Lattice,
        outputs: &mut [&mut DataflowOutput<Self::Lattice>],
    );

    fn run(&mut self, scratch: &mut DataflowScratch<Self::Lattice>) {
        let body = self.body();

        scratch.reset(body, |is_entry| self.init_effect(is_entry));

        while let Some(curr) = scratch.worklist.pop_front() {
            let curr_indices = scratch.basic_block_indices[curr];

            // Join block predecessors
            {
                let mut borrows = scratch
                    .effect_elems_borrow
                    .builder(&mut scratch.effect_elems);

                let predecessors = scratch.ptr_scratch.build(
                    (curr_indices.first_predecessor_idx..)
                        .take(body.cfg.block_predecessors(curr).len())
                        .map(|idx| &borrows.get(idx as usize).value),
                );

                let successor = borrows.get_mut(curr_indices.join_out_idx as usize);

                // N.B. we reuse this flag to both detect whether `trans_join` has updated its
                // entrypoint effect to a new value and to mark blocks as queued in the worklist.
                assert!(successor.is_dirty);
                successor.is_dirty = false;

                self.trans_join(predecessors, successor);

                if !mem::take(&mut successor.is_dirty) {
                    // The input effect to the block has not actually changed, even though its
                    // predecessors have changed.
                    continue;
                }
            }

            // Transition statements
            enum TerminatorInput<'a, T> {
                AtIdx(usize),
                ByRef(&'a T),
            }

            let terminator_input = 'stmt: {
                let mut iter = body.cfg.block_stmts(curr, MirBodyDirection::Forwards);

                let [scratch_src, scratch_dst] = scratch.stmt_tmp_effects.as_mut().unwrap();
                let mut scratch_src = scratch_src;
                let mut scratch_dst = scratch_dst;

                if let Some(stmt) = iter.next() {
                    self.trans_stmt(
                        stmt,
                        &scratch.effect_elems[curr_indices.join_out_idx as usize].value,
                        scratch_src,
                    );
                } else {
                    break 'stmt TerminatorInput::AtIdx(curr_indices.join_out_idx as usize);
                }

                for stmt in iter {
                    self.trans_stmt(stmt, scratch_src, scratch_dst);

                    mem::swap(&mut scratch_dst, &mut scratch_src);
                }

                TerminatorInput::ByRef(scratch_src)
            };

            // Transition terminator
            {
                let mut borrows = scratch
                    .effect_elems_borrow
                    .builder(&mut scratch.effect_elems);

                let input = match terminator_input {
                    TerminatorInput::AtIdx(idx) => &borrows.get(idx).value,
                    TerminatorInput::ByRef(v) => v,
                };

                let outputs = body.cfg.block_successors(curr).iter().map(|link| {
                    let base = scratch.basic_block_indices[link.target].first_predecessor_idx;
                    borrows.get_mut(base as usize + link.at_idx)
                });
                let outputs = scratch.ptr_scratch.build(outputs);

                self.trans_terminator(curr, input, outputs);

                for (&succ, output) in body.cfg.block_successors(curr).iter().zip(outputs) {
                    if !mem::take(&mut output.is_dirty) {
                        continue;
                    }

                    let slot = borrows
                        .get_mut(scratch.basic_block_indices[succ.target].join_out_idx as usize);

                    if slot.is_dirty {
                        continue;
                    }

                    slot.is_dirty = true;
                    scratch.worklist.push_back(succ.target);
                }
            }
        }

        scratch.trim();
    }
}

// === DataflowScratch === //

#[derive_where(Default)]
pub struct DataflowScratch<T> {
    /// A worklist of basic blocks whose predecessors have been updated.
    worklist: VecDeque<MirBlockIdx>,

    /// A set of effect lattice values, which are intended to be reused in place as lattice elements
    /// pass through transfer functions. The first portion of the array corresponds to block initial
    /// states and the remainder corresponds to predecessor stashes.
    effect_elems: Vec<DataflowOutput<T>>,

    /// A mapping from basic blocks to their predecessor and successor entries in `effect_elems`
    basic_block_indices: SecondaryMap<MirBlockIdx, BasicBlockState>,

    /// A temporary pair of effects for transferring lattice states between statements.
    stmt_tmp_effects: Option<[T; 2]>,

    /// A data-structure for managing disjoint borrows of `effect_elems`.
    effect_elems_borrow: DisjointBorrowsScratch,

    /// A scratch buffer for storing vectors of references.
    ptr_scratch: VecOfPtrScratch,
}

#[derive(Copy, Clone)]
struct BasicBlockState {
    /// The effect state at the beginning of a block. The dirty flag plays dual purpose as both an
    /// indicator of whether the block is in the worklist and, when updating the join for the block,
    /// an indicator of whether the block's entry effect actually changed.
    join_out_idx: u32,

    /// The index of the first predecessor's output effect into this successor.
    first_predecessor_idx: u32,
}

impl<T> DataflowScratch<T> {
    fn reset(&mut self, body: &MirBody, mut init_effect: impl FnMut(bool) -> T) {
        self.worklist.clear();
        self.effect_elems.clear();
        self.basic_block_indices.clear();

        self.stmt_tmp_effects = Some([init_effect(false), init_effect(false)]);

        for block in body.cfg.blocks() {
            self.basic_block_indices.insert(
                block,
                BasicBlockState {
                    join_out_idx: self.effect_elems.len() as u32,
                    first_predecessor_idx: u32::MAX,
                },
            );

            self.effect_elems.push(DataflowOutput {
                is_dirty: true,
                value: init_effect(block == body.entry),
            });

            self.worklist.push_back(block);
        }

        for block in body.cfg.blocks() {
            let predecessors = body.cfg.block_predecessors(block);

            if predecessors.is_empty() {
                continue;
            }

            assert!(block != body.entry);

            self.basic_block_indices[block].first_predecessor_idx = self.effect_elems.len() as u32;

            for _ in 0..predecessors.len() {
                self.effect_elems.push(DataflowOutput {
                    is_dirty: false,
                    value: init_effect(false),
                });
            }
        }
    }

    fn trim(&mut self) {
        self.worklist.clear();
        self.effect_elems.clear();
        self.basic_block_indices.clear();
        self.stmt_tmp_effects = None;
    }
}

// === DataflowOutput === //

pub struct DataflowOutput<T> {
    pub is_dirty: bool,
    pub value: T,
}
