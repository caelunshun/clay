use crate::{
    base::{Diag, arena::Obj},
    semantic::{
        analysis::{
            borrowck::check::{
                analysis::{LivenessAnalysis, OccupancyAnalysis, OccupancyAnalysisMode},
                dataflow::{
                    BackwardsDataflowAnalysis, DataflowScratch, DataflowView,
                    ForwardsDataflowAnalysis as _,
                },
                places::{PlaceNumbering, PlaceSet, number_places_in_body},
            },
            sigck::CrateSigckVisitor,
        },
        syntax::{FnDef, MirBodyDirection, MirPlaceMention, MirPlaceMentionKind, TraverseMentions},
    },
};
use std::fmt;

pub fn run_borrow_check(cx: &mut CrateSigckVisitor, def: Obj<FnDef>) {
    let s = cx.session();
    let tcx = cx.tcx();

    let Some(body) = &*def.r(s).mir_body else {
        return;
    };

    // Analyze dataflow facts about body
    let place_numbering = number_places_in_body(tcx, body);

    let mut liveness_scratch = DataflowScratch::default();
    let mut liveness_analysis = LivenessAnalysis {
        tcx,
        body,
        place_numbering: &place_numbering,
    };

    liveness_analysis.run(&mut liveness_scratch);

    let mut occupancy_scratch = DataflowScratch::default();
    let mut occupancy_analysis = OccupancyAnalysis {
        tcx,
        body,
        place_numbering: &place_numbering,
        mode: OccupancyAnalysisMode::May,
    };

    occupancy_analysis.run(&mut occupancy_scratch);

    let mut occupancy_iter =
        DataflowView::new_forwards(&mut occupancy_analysis, &mut occupancy_scratch);

    // Check ownership
    fn process_mentions(
        mut state: PlaceSet,
        place_numbering: &PlaceNumbering,
        mentions: &[MirPlaceMention],
        src_info: impl fmt::Debug,
    ) {
        for mention in mentions {
            if mention.kind.intersects(MirPlaceMentionKind::OCCUPANCY_ADD) {
                state.add(place_numbering, mention.place);
            }

            if mention
                .kind
                .intersects(MirPlaceMentionKind::OCCUPANCY_ACCESS)
                && !state.has(place_numbering, mention.place)
            {
                Diag::anon_err(format_args!("oh no! {src_info:?}")).emit();
            }

            if mention.kind.intersects(MirPlaceMentionKind::OCCUPANCY_DEAD) {
                state.remove(place_numbering, mention.place);
            }
        }
    }

    for block in body.blocks() {
        for stmt in block.stmts(MirBodyDirection::Forwards) {
            process_mentions(
                occupancy_iter.trans_before(stmt.stmt).clone(),
                &place_numbering,
                &stmt.kind().mentions(tcx),
                stmt.stmt(),
            );
        }

        process_mentions(
            occupancy_iter.trans_before_end(block.block).clone(),
            &place_numbering,
            &block.terminator_kind().mentions(tcx),
            block.terminator(),
        );
    }
}
