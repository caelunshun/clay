use crate::{
    semantic::syntax::{MirBlockIdx, MirBody, MirBodyDirection, MirStmtIdx},
    utils::mem::{DisjointBorrowsScratch, VecOfPtrScratch},
};
use bytemuck::TransparentWrapper;
use derive_where::derive_where;
use slotmap::SecondaryMap;
use std::{collections::VecDeque, mem};

// === DataflowAnalysis === //

pub trait ForwardsDataflowAnalysis<'g> {
    type Lattice;

    fn body(&self) -> &'g MirBody;

    fn init_effect(&mut self, is_entry: bool) -> Self::Lattice;

    fn trans_stmt(&mut self, idx: MirStmtIdx, input: &Self::Lattice, output: &mut Self::Lattice);

    fn trans_join(&mut self, inputs: &[&Self::Lattice], output: &mut DataflowOutput<Self::Lattice>);

    fn trans_terminator(
        &mut self,
        idx: MirBlockIdx,
        input: &Self::Lattice,
        outputs: &mut [&mut DataflowOutput<Self::Lattice>],
    );

    fn run(&mut self, scratch: &mut DataflowScratch<Self::Lattice>) {
        let body = self.body();

        // Initialize scratch
        scratch.worklist.clear();
        scratch.effect_elems.clear();
        scratch.basic_block_indices.clear();

        scratch.stmt_tmp_effects = Some([
            DataflowOutput {
                is_dirty: true,
                value: self.init_effect(false),
            },
            DataflowOutput {
                is_dirty: true,
                value: self.init_effect(false),
            },
        ]);

        for block in body.cfg.blocks() {
            scratch.basic_block_indices.insert(
                block,
                BasicBlockState {
                    seed_idx: scratch.effect_elems.len() as u32,
                    aux_idx: u32::MAX,
                },
            );

            scratch.effect_elems.push(DataflowOutput {
                is_dirty: true,
                value: self.init_effect(block == body.entry),
            });

            scratch.worklist.push_back(block);
        }

        for block in body.cfg.blocks() {
            let predecessors = body.cfg.block_predecessors(block);

            if predecessors.is_empty() {
                continue;
            }

            assert!(block != body.entry);

            scratch.basic_block_indices[block].aux_idx = scratch.effect_elems.len() as u32;

            for _ in 0..predecessors.len() {
                scratch.effect_elems.push(DataflowOutput {
                    is_dirty: false,
                    value: self.init_effect(false),
                });
            }
        }

        // Run dataflow
        while let Some(curr) = scratch.worklist.pop_front() {
            let curr_indices = scratch.basic_block_indices[curr];

            // Join block predecessors
            {
                let mut borrows = scratch
                    .effect_elems_borrow
                    .builder(&mut scratch.effect_elems);

                let predecessors = scratch.ptr_scratch.build(
                    (curr_indices.aux_idx..)
                        .take(body.cfg.block_predecessors(curr).len())
                        .map(|idx| &borrows.get(idx as usize).value),
                );

                let successor = borrows.get_mut(curr_indices.seed_idx as usize);

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
                        &scratch.effect_elems[curr_indices.seed_idx as usize].value,
                        &mut scratch_src.value,
                    );
                } else {
                    break 'stmt TerminatorInput::AtIdx(curr_indices.seed_idx as usize);
                }

                for stmt in iter {
                    self.trans_stmt(stmt, &scratch_src.value, &mut scratch_dst.value);

                    mem::swap(&mut scratch_dst, &mut scratch_src);
                }

                TerminatorInput::ByRef(&scratch_src.value)
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
                    let base = scratch.basic_block_indices[link.target].aux_idx;
                    borrows.get_mut(base as usize + link.at_idx)
                });
                let outputs = scratch.ptr_scratch.build(outputs);

                self.trans_terminator(curr, input, outputs);

                for (&succ, output) in body.cfg.block_successors(curr).iter().zip(outputs) {
                    if !mem::take(&mut output.is_dirty) {
                        continue;
                    }

                    let slot =
                        borrows.get_mut(scratch.basic_block_indices[succ.target].seed_idx as usize);

                    if slot.is_dirty {
                        continue;
                    }

                    slot.is_dirty = true;
                    scratch.worklist.push_back(succ.target);
                }
            }
        }

        // Trim unnecessary lattices
        scratch.effect_elems.truncate(body.cfg.blocks().len());
        scratch.stmt_tmp_effects = None;
    }
}

pub trait BackwardsDataflowAnalysis<'g> {
    type Lattice;

    fn body(&self) -> &'g MirBody;

    fn init_effect(&mut self) -> Self::Lattice;

    fn trans_stmt(
        &mut self,
        idx: MirStmtIdx,
        input: &Self::Lattice,
        output: &mut DataflowOutput<Self::Lattice>,
    );

    fn trans_terminator(
        &mut self,
        idx: MirBlockIdx,
        inputs: &[&Self::Lattice],
        outputs: &mut DataflowOutput<Self::Lattice>,
    );

    fn run(&mut self, scratch: &mut DataflowScratch<Self::Lattice>) {
        let body = self.body();

        // Initialize scratch
        scratch.worklist.clear();
        scratch.effect_elems.clear();
        scratch.basic_block_indices.clear();

        scratch.stmt_tmp_effects = Some([
            DataflowOutput {
                is_dirty: true,
                value: self.init_effect(),
            },
            DataflowOutput {
                is_dirty: true,
                value: self.init_effect(),
            },
        ]);

        for block in body.cfg.blocks() {
            let seed_idx = scratch.effect_elems.len() as u32;

            scratch.basic_block_indices.insert(
                block,
                BasicBlockState {
                    seed_idx,
                    // Will get initialized to a disjoint slot if the block is non-empty.
                    aux_idx: seed_idx,
                },
            );

            scratch.effect_elems.push(DataflowOutput {
                is_dirty: true,
                value: self.init_effect(),
            });

            scratch.worklist.push_back(block);
        }

        for block in body.cfg.blocks() {
            if body.cfg.block_first(block).is_none() {
                continue;
            }

            scratch.basic_block_indices[block].aux_idx = scratch.effect_elems.len() as u32;

            scratch.effect_elems.push(DataflowOutput {
                is_dirty: false,
                value: self.init_effect(),
            });
        }

        // Run dataflow
        while let Some(curr) = scratch.worklist.pop_front() {
            let curr_indices = scratch.basic_block_indices[curr];

            // Join terminator successors
            {
                let mut borrows = scratch
                    .effect_elems_borrow
                    .builder(&mut scratch.effect_elems);

                let inputs = scratch
                    .ptr_scratch
                    .build(body.cfg.block_successors(curr).iter().map(|&succ| {
                        &borrows
                            .get(scratch.basic_block_indices[succ.target].aux_idx as usize)
                            .value
                    }));

                let output = borrows.get_mut(curr_indices.seed_idx as usize);

                // N.B. we reuse this flag to both detect whether `trans_terminator` has updated its
                // entrypoint effect to a new value and to mark blocks as queued in the worklist.
                assert!(output.is_dirty);
                output.is_dirty = false;

                self.trans_terminator(curr, inputs, output);

                if !mem::take(&mut output.is_dirty) {
                    // The input effect to the block has not actually changed, even though its
                    // predecessors have changed.
                    continue;
                }
            }

            // Transition statements
            // N.B. No, this is not a typo. We're referring to statements by their iteration order!
            let [Some(first_stmt), Some(last_stmt)] =
                [body.cfg.block_last(curr), body.cfg.block_first(curr)]
            else {
                continue;
            };

            let [first_stmt_slot, last_stmt_slot] = scratch
                .effect_elems
                .get_disjoint_mut([
                    curr_indices.seed_idx as usize,
                    curr_indices.aux_idx as usize,
                ])
                .unwrap();

            let [scratch_src, scratch_dst] = scratch.stmt_tmp_effects.as_mut().unwrap();
            let mut scratch_src = scratch_src;
            let mut scratch_dst = scratch_dst;

            for stmt in body.cfg.block_stmts(curr, MirBodyDirection::Backwards) {
                self.trans_stmt(
                    stmt,
                    if stmt == first_stmt {
                        &first_stmt_slot.value
                    } else {
                        &scratch_src.value
                    },
                    if stmt == last_stmt {
                        last_stmt_slot
                    } else {
                        scratch_dst
                    },
                );

                mem::swap(&mut scratch_src, &mut scratch_dst);
            }

            if !mem::take(&mut last_stmt_slot.is_dirty) {
                // The `aux_idx` hasn't changed so our predecessors won't observe a change.
                continue;
            }

            // Add predecessors to worklist.
            for pred in body.cfg.block_predecessors(curr) {
                let pred_seed = scratch.basic_block_indices[pred.target].seed_idx;
                let pred_seed = &mut scratch.effect_elems[pred_seed as usize];

                if pred_seed.is_dirty {
                    continue;
                }

                pred_seed.is_dirty = true;
                scratch.worklist.push_back(pred.target);
            }
        }

        // Trim unnecessary lattices
        scratch.effect_elems.truncate(body.cfg.blocks().len());
        scratch.stmt_tmp_effects = None;
    }
}

// === DataflowIter === //

pub struct DataflowIter<'a, 'g, T> {
    analysis: &'a mut dyn AnyDataflowAnalysis<'g, Lattice = T>,
    scratch: &'a DataflowScratch<T>,
}

trait AnyDataflowAnalysis<'g> {
    type Lattice;

    fn body(&self) -> &'g MirBody;

    fn trans_stmt(&mut self, idx: MirStmtIdx, input: &Self::Lattice, output: &mut Self::Lattice);
}

#[derive(TransparentWrapper)]
#[repr(transparent)]
struct ForwardsDataflowAnalysisWrapper<T: ?Sized>(T);

// === DataflowScratch === //

#[derive_where(Default)]
pub struct DataflowScratch<T> {
    /// A worklist of basic blocks whose dependencies have been updated.
    worklist: VecDeque<MirBlockIdx>,

    /// A set of effect lattice values, which are intended to be reused in place as lattice elements
    /// pass through transfer functions. The first portion of the vector is dedicated to block seed
    /// effects to simplify the process of trimming.
    effect_elems: Vec<DataflowOutput<T>>,

    /// A mapping from basic blocks to their entries in `effect_elems`
    basic_block_indices: SecondaryMap<MirBlockIdx, BasicBlockState>,

    /// A temporary pair of effects for transferring lattice states between statements.
    stmt_tmp_effects: Option<[DataflowOutput<T>; 2]>,

    /// A data-structure for managing disjoint borrows of `effect_elems`.
    effect_elems_borrow: DisjointBorrowsScratch,

    /// A scratch buffer for storing vectors of references.
    ptr_scratch: VecOfPtrScratch,
}

#[derive(Copy, Clone)]
struct BasicBlockState {
    /// The effect state at the beginning of a block. The dirty flag plays dual purpose as both an
    /// indicator of whether the block is in the worklist and for detecting transfer function dirty
    /// operation.
    seed_idx: u32,

    /// An auxiliary index whose interpretation depends on whether this is a forwards or a backwards
    /// analysis.
    ///
    /// If the analysis is forwards, this encodes the index of the first predecessor's output effect
    /// into this block.
    ///
    /// If the analysis is backwards, this encodes the index of the state of the block after the
    /// first statement. If the block is empty, this will equal the `seed_idx`.
    aux_idx: u32,
}

// === DataflowOutput === //

pub struct DataflowOutput<T> {
    pub is_dirty: bool,
    pub value: T,
}
