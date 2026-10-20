use crate::semantic::{
    analysis::borrowck::check::{
        dataflow::{BackwardsDataflowAnalysis, DataflowOutput, ForwardsDataflowAnalysis},
        places::{PlaceNumbering, PlaceSet},
    },
    syntax::{
        MirBlockRef, MirBody, MirPlace, MirPlaceMentionKind, MirStmtRef, MirTerminatorSuccessor,
        TraverseMentions, TyCtxt,
    },
};

// === LivenessAnalysis === //

pub struct LivenessAnalysis<'g> {
    pub tcx: &'g TyCtxt,
    pub body: &'g MirBody,
    pub place_numbering: &'g PlaceNumbering,
}

impl<'g> BackwardsDataflowAnalysis<'g> for LivenessAnalysis<'g> {
    type Lattice = PlaceSet;

    fn body(&self) -> &'g MirBody {
        self.body
    }

    fn init_effect(&mut self) -> Self::Lattice {
        PlaceSet::default()
    }

    fn trans_stmt(
        &mut self,
        stmt: MirStmtRef<'g>,
        input: &Self::Lattice,
        output: &mut DataflowOutput<Self::Lattice>,
    ) {
        let mut new_output = input.clone();

        for &mention in stmt.kind().mentions(self.tcx).iter().rev() {
            if mention.kind.intersects(MirPlaceMentionKind::LIVENESS_USE) {
                new_output.add(self.place_numbering, mention.place);
            }

            if mention.kind.intersects(MirPlaceMentionKind::LIVENESS_INIT) {
                new_output.remove(self.place_numbering, mention.place);
            }
        }

        output.set_value(new_output);
    }

    fn trans_terminator(
        &mut self,
        block: MirBlockRef<'g>,
        inputs: &[&Self::Lattice],
        output: &mut DataflowOutput<Self::Lattice>,
    ) {
        let mut new_output_success = PlaceSet::default();
        let mut new_output_unwind = PlaceSet::default();

        for (successor, &effect) in block.terminator_kind().successors().iter().zip(inputs) {
            if successor.is_unwind {
                new_output_unwind.union(effect);
            } else {
                new_output_success.union(effect);
            }
        }

        for &mention in block.terminator_kind().mentions(self.tcx).iter().rev() {
            if mention.kind.intersects(MirPlaceMentionKind::LIVENESS_USE) {
                new_output_success.add(self.place_numbering, mention.place);
                new_output_unwind.add(self.place_numbering, mention.place);
            }

            if mention.kind.intersects(MirPlaceMentionKind::LIVENESS_INIT) {
                new_output_success.remove(self.place_numbering, mention.place);
            }
        }

        new_output_success.union(&new_output_unwind);
        output.set_value(new_output_success);
    }
}

// === OccupancyAnalysis === //

pub struct OccupancyAnalysis<'g> {
    pub tcx: &'g TyCtxt,
    pub body: &'g MirBody,
    pub place_numbering: &'g PlaceNumbering,
    pub mode: OccupancyAnalysisMode,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum OccupancyAnalysisMode {
    Must,
    May,
}

impl<'g> ForwardsDataflowAnalysis<'g> for OccupancyAnalysis<'g> {
    type Lattice = PlaceSet;

    fn body(&self) -> &'g MirBody {
        self.body
    }

    fn init_effect(&mut self, is_entry: bool) -> Self::Lattice {
        let mut set = PlaceSet::default();

        if is_entry {
            for local in self.body.arg_locals() {
                set.add(self.place_numbering, MirPlace::new(self.tcx, local, []));
            }
        }

        set
    }

    fn trans_join(
        &mut self,
        inputs: &[&Self::Lattice],
        output: &mut DataflowOutput<Self::Lattice>,
    ) {
        let Some((&first, remainder)) = inputs.split_first() else {
            // keep existing initial `output`.
            return;
        };

        let mut new_output = first.clone();

        for &remainder in remainder {
            match self.mode {
                OccupancyAnalysisMode::Must => {
                    new_output.intersect(remainder);
                }
                OccupancyAnalysisMode::May => {
                    new_output.union(remainder);
                }
            }
        }

        output.set_value(new_output);
    }

    fn trans_stmt(
        &mut self,
        stmt: MirStmtRef<'g>,
        input: &Self::Lattice,
        output: &mut Self::Lattice,
    ) {
        output.clone_from(input);

        for mention in stmt.kind().mentions(self.tcx) {
            if mention.kind.intersects(MirPlaceMentionKind::OCCUPANCY_ADD) {
                output.add(self.place_numbering, mention.place);
            }

            if mention.kind.intersects(MirPlaceMentionKind::OCCUPANCY_DEAD) {
                output.remove(self.place_numbering, mention.place);
            }
        }
    }

    fn trans_terminator(
        &mut self,
        block: MirBlockRef<'g>,
        input: &Self::Lattice,
        outputs: &mut [&mut DataflowOutput<Self::Lattice>],
    ) {
        let mut new_output_success = input.clone();
        let mut new_output_unwind = input.clone();

        for mention in block.terminator_kind().mentions(self.tcx) {
            if mention.kind.intersects(MirPlaceMentionKind::OCCUPANCY_ADD) {
                new_output_success.add(self.place_numbering, mention.place);
            }

            if mention.kind.intersects(MirPlaceMentionKind::OCCUPANCY_DEAD) {
                new_output_success.remove(self.place_numbering, mention.place);
                new_output_unwind.remove(self.place_numbering, mention.place);
            }
        }

        for (output, MirTerminatorSuccessor { is_unwind, .. }) in
            outputs.iter_mut().zip(block.terminator_kind().successors())
        {
            output.set_value_ref(if is_unwind {
                &new_output_unwind
            } else {
                &new_output_success
            });
        }
    }
}
