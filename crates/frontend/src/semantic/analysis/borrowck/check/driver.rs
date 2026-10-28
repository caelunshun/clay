use crate::{
    base::{Diag, arena::Obj},
    flags,
    semantic::{
        analysis::{
            borrowck::check::{
                analysis::{LivenessAnalysis, OccupancyAnalysis, OccupancyAnalysisMode},
                dataflow::{
                    BackwardsDataflowAnalysis, DataflowScratch, DataflowView,
                    ForwardsDataflowAnalysis as _,
                },
                places::{AtomicSubPlaceIdx, PlaceNumbering, PlaceSet, number_places_in_body},
            },
            sigck::CrateSigckVisitor,
        },
        infer::{ClauseCx, UnifyCxMode},
        syntax::{
            FnDef, MirBodyDirection, MirLocationAfter, MirPlaceMention, MirPlaceMentionKind,
            MirPrettyFmt, RelationDirection, TraverseMentions, UniversalReVarSourceInfo,
        },
    },
};
use index_vec::IndexVec;
use std::fmt::{self, Display as _};

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

    let mut liveness_iter =
        DataflowView::new_backwards(&mut liveness_analysis, &mut liveness_scratch);

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
        src_info: impl fmt::Display,
    ) {
        for mention in mentions {
            if mention.kind.intersects(MirPlaceMentionKind::OCCUPANCY_ADD) {
                state.add_place(place_numbering, mention.place);
            }

            if mention
                .kind
                .intersects(MirPlaceMentionKind::OCCUPANCY_ACCESS)
                && !state.has_place(place_numbering, mention.place)
            {
                Diag::anon_err(format_args!("oh no! {src_info}")).emit();
            }

            if mention.kind.intersects(MirPlaceMentionKind::OCCUPANCY_DEAD) {
                state.remove_place(place_numbering, mention.place);
            }
        }
    }

    let fmt_cx = MirPrettyFmt::new(tcx, body);

    if flags::should_print_mir_dataflow() {
        println!(
            "{}",
            occupancy_iter.annotated_flat_body(fmt_cx, |set, f| {
                set.pretty(&fmt_cx, &place_numbering).fmt(f)
            })
        );
    }

    for block in body.blocks() {
        for stmt in block.stmts(MirBodyDirection::Forwards) {
            process_mentions(
                occupancy_iter.trans_before(stmt.stmt).clone(),
                &place_numbering,
                &stmt.kind().mentions(tcx),
                fmt_cx.plain_stmt(stmt.stmt()),
            );
        }

        process_mentions(
            occupancy_iter.trans_before_end(block.block).clone(),
            &place_numbering,
            &block.terminator_kind().mentions(tcx),
            fmt_cx.plain_terminator(block.terminator()),
        );
    }

    // Check regions
    let mut ccx = ClauseCx::new(tcx, &cx.impl_cache, cx.krate, UnifyCxMode::RegionAware);
    let env = ccx.universal_env_for_fn_def(def);

    let place_universals = place_numbering
        .bit_to_place
        .iter()
        .map(|&place| ccx.fresh_re_universal(UniversalReVarSourceInfo::MirPlace(place)))
        .collect::<IndexVec<AtomicSubPlaceIdx, _>>();

    // TODO: make this not `O(n^2)`.
    for rhs in place_numbering.bit_to_place.indices() {
        // Determine which other *locals* the `rhs` can outlive.
        //
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
        let mut outlive_mask = PlaceSet::default();
        outlive_mask.fill(&place_numbering);

        fn refine_outlive_mask(
            mask: &mut PlaceSet,
            rhs: AtomicSubPlaceIdx,
            liveness: &PlaceSet,
            occupancy: &PlaceSet,
        ) {
            if !liveness.has_one(rhs) {
                return;
            }

            mask.intersect(occupancy);
        }

        for block in body.blocks() {
            refine_outlive_mask(
                &mut outlive_mask,
                rhs,
                liveness_iter.natural_after(MirLocationAfter::BlockStart(block.block)),
                occupancy_iter.natural_after(MirLocationAfter::BlockStart(block.block)),
            );

            for stmt in block.stmts(MirBodyDirection::Forwards) {
                refine_outlive_mask(
                    &mut outlive_mask,
                    rhs,
                    // TODO: use better cache access patterns
                    liveness_iter.natural_after(MirLocationAfter::Stmt(stmt.stmt)),
                    occupancy_iter.natural_after(MirLocationAfter::Stmt(stmt.stmt)),
                );
            }
        }

        for lhs in outlive_mask.iter() {
            ccx.permit_universe_re_outlives_re(
                place_universals[lhs],
                place_universals[rhs],
                RelationDirection::LhsOntoRhs,
            );
        }

        // TODO: longer than env universals
    }
}
