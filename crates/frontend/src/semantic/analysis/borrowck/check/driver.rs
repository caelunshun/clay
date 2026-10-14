use crate::{
    base::arena::Obj,
    semantic::{
        analysis::{
            borrowck::check::{
                analysis::LivenessAnalysis,
                dataflow::{BackwardsDataflowAnalysis, DataflowScratch},
                places::number_places_in_body,
            },
            sigck::CrateSigckVisitor,
        },
        syntax::FnDef,
    },
};

pub fn run_borrow_check(cx: &mut CrateSigckVisitor, def: Obj<FnDef>) {
    let s = cx.session();
    let tcx = cx.tcx();

    let Some(body) = &*def.r(s).mir_body else {
        return;
    };

    let place_numbering = number_places_in_body(tcx, body);

    let mut liveness_scratch = DataflowScratch::default();
    let mut liveness_analysis = LivenessAnalysis {
        tcx,
        body,
        place_numbering: &place_numbering,
    };

    liveness_analysis.run(&mut liveness_scratch);
}
