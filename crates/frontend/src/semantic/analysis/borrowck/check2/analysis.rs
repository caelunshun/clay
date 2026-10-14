use crate::semantic::{
    analysis::borrowck::check2::{
        dataflow::{BackwardsDataflowAnalysis, DataflowOutput},
        places::{PlaceNumbering, PlaceSet},
    },
    syntax::{MirBlockIdx, MirBody, MirStmtIdx, TyCtxt},
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
        idx: MirStmtIdx,
        input: &Self::Lattice,
        output: &mut DataflowOutput<Self::Lattice>,
    ) {
        todo!()
    }

    fn trans_terminator(
        &mut self,
        idx: MirBlockIdx,
        inputs: &[&Self::Lattice],
        outputs: &mut DataflowOutput<Self::Lattice>,
    ) {
        todo!()
    }
}
