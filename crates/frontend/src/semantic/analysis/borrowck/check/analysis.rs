use crate::semantic::{
    analysis::borrowck::check::{
        dataflow::{BackwardsDataflowAnalysis, DataflowOutput},
        places::{PlaceNumbering, PlaceSet},
    },
    syntax::{MirBlockRef, MirBody, MirPlaceMentionKind, MirStmtRef, TraverseMentions, TyCtxt},
};

// === LivenessAnalysis === //

pub struct LivenessAnalysis<'g> {
    tcx: &'g TyCtxt,
    body: &'g MirBody,
    place_numbering: &'g PlaceNumbering,
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

        for (successor, &effect) in block.terminator().successors().iter().zip(inputs) {
            if successor.is_unwind {
                new_output_unwind.union(effect);
            } else {
                new_output_success.union(effect);
            }
        }

        for &mention in block.terminator().mentions(self.tcx).iter().rev() {
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
