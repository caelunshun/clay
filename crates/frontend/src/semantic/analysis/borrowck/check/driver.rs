use crate::{
    base::{
        Diag, Session,
        arena::{HasInterner, HasListInterner, Obj},
    },
    flags,
    semantic::{
        analysis::{
            borrowck::check::{
                analysis::{LivenessAnalysis, OccupancyAnalysis, OccupancyAnalysisMode},
                dataflow::{
                    BackwardsDataflowAnalysis, DataflowScratch, DataflowView,
                    ForwardsDataflowAnalysis as _,
                },
                places::{
                    AtomicPlaceIdx, PlaceNumbering, PlaceSet, is_place_direct,
                    number_places_in_body,
                },
            },
            sigck::CrateSigckVisitor,
        },
        infer::{
            ClauseCx, ClauseImportEnv, ClausePrettyFmtOpts, GenericSubst, MirSpannedError,
            UnifyCxMode,
        },
        syntax::{
            AdtInstance, FnDef, MirBlockIdx, MirBody, MirBodyDirection, MirLocalIdx,
            MirLocationAfter, MirPlace, MirPlaceElem, MirPlaceMention, MirPlaceMentionKind,
            MirPrettyFmt, MirPrettyFmtHooks, MirRvalue, MirSourceInfo, MirStmtIdx, MirStmtKind,
            MirStraightBinOpKind, MirStraightUnOpKind, MirTerminatorKind, Re, RelationDirection,
            RelationMode, ResolvedFieldIdx, SimpleTyKind, TraverseMentions, Ty, TyCtxt, TyKind,
            TyOrRe, UniversalReVarSourceInfo,
        },
    },
    utils::lang::NewtypedRangeExt as _,
};
use index_vec::IndexVec;
use std::{cell::RefCell, fmt};

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
        s: &Session,
        mut state: PlaceSet,
        place_numbering: &PlaceNumbering,
        mentions: &[MirPlaceMention],
        src_info: impl fmt::Display,
    ) {
        for mention in mentions {
            if !is_place_direct(s, mention.place) {
                continue;
            }

            if mention.kind.intersects(MirPlaceMentionKind::OCCUPANCY_ADD) {
                state.add_place(s, place_numbering, mention.place);
            }

            if mention
                .kind
                .intersects(MirPlaceMentionKind::OCCUPANCY_ACCESS)
                && !state.has_place(s, place_numbering, mention.place)
            {
                Diag::anon_err(format_args!("oh no! {src_info}")).emit();
            }

            if mention.kind.intersects(MirPlaceMentionKind::OCCUPANCY_DEAD) {
                state.remove_place(s, place_numbering, mention.place);
            }
        }
    }

    let fmt_cx = MirPrettyFmt::new(tcx, body);

    if flags::should_print_mir_dataflow() {
        pub struct FmtHooks<'r, 'a> {
            liveness_iter: RefCell<&'r mut DataflowView<'a, PlaceSet>>,
            occupancy_iter: RefCell<&'r mut DataflowView<'a, PlaceSet>>,
            place_numbering: &'r PlaceNumbering,
        }

        impl FmtHooks<'_, '_> {
            fn print_at(
                &self,
                cx: &MirPrettyFmt<'_>,
                f: &mut fmt::Formatter,
                place: MirLocationAfter,
            ) -> fmt::Result {
                writeln!(
                    f,
                    "// live: {}; occupied: {}",
                    self.liveness_iter
                        .borrow_mut()
                        .natural_after(place)
                        .pretty(cx, self.place_numbering),
                    self.occupancy_iter
                        .borrow_mut()
                        .natural_after(place)
                        .pretty(cx, self.place_numbering)
                )
            }
        }

        impl<'r, 'a> MirPrettyFmtHooks for FmtHooks<'r, 'a> {
            fn start_of_block(
                &self,
                cx: &MirPrettyFmt<'_>,
                f: &mut fmt::Formatter<'_>,
                block: MirBlockIdx,
            ) -> fmt::Result {
                self.print_at(cx, f, MirLocationAfter::BlockStart(block))
            }

            fn after_stmt(
                &self,
                cx: &MirPrettyFmt<'_>,
                f: &mut fmt::Formatter<'_>,
                stmt: MirStmtIdx,
            ) -> fmt::Result {
                self.print_at(cx, f, MirLocationAfter::Stmt(stmt))
            }
        }

        println!(
            "{}",
            fmt_cx
                .with_hooks(&FmtHooks {
                    liveness_iter: RefCell::new(&mut liveness_iter),
                    occupancy_iter: RefCell::new(&mut occupancy_iter),
                    place_numbering: &place_numbering,
                })
                .flat_body()
        );
    }

    for block in body.blocks() {
        for stmt in block.stmts(MirBodyDirection::Forwards) {
            process_mentions(
                s,
                occupancy_iter.trans_before(stmt.stmt).clone(),
                &place_numbering,
                &stmt.kind().mentions(tcx),
                fmt_cx.plain_stmt(stmt.stmt()),
            );
        }

        process_mentions(
            s,
            occupancy_iter.trans_before_end(block.block).clone(),
            &place_numbering,
            &block.terminator_kind().mentions(tcx),
            fmt_cx.plain_terminator(block.terminator()),
        );
    }

    // Check regions
    let mut ccx = ClauseCx::new(tcx, &cx.impl_cache, cx.krate, UnifyCxMode::RegionAware);
    let env = ccx.universal_env_for_fn_def(def);
    // TODO: add dyn-site universals to environment

    let shortest_sig_universal = ccx.fresh_re_infer();

    let atomic_place_universals = place_numbering
        .bit_to_atomic_place
        .iter()
        .map(|&place| ccx.fresh_re_universal(UniversalReVarSourceInfo::MirPlace(place)))
        .collect::<IndexVec<AtomicPlaceIdx, Re>>();

    let imported_locals = body
        .locals
        .iter()
        .map(|&local| ccx.import_elsewhere(&env, local.ty))
        .collect::<IndexVec<MirLocalIdx, Ty>>();

    for &var in env.generics.iter().flat_map(|v| v.substs.r(s)) {
        match var {
            TyOrRe::Re(var) => {
                ccx.ucx_mut()
                    .unify_re_and_re(var, shortest_sig_universal, RelationMode::LhsOntoRhs)
                    .report_never();
            }
            TyOrRe::Ty(ty) => {
                ccx.oblige_ty_outlives_re(
                    ty,
                    shortest_sig_universal,
                    RelationDirection::LhsOntoRhs,
                )
                .report_never();
            }
        }
    }

    // TODO: make this not `O(n^2)`.
    for rhs in place_numbering.bit_to_atomic_place.indices() {
        // All locals live shorter than our signature universals
        ccx.permit_universe_re_outlives_re(
            atomic_place_universals[rhs],
            shortest_sig_universal,
            RelationDirection::RhsOntoLhs,
        );

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
            rhs: AtomicPlaceIdx,
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
                atomic_place_universals[lhs],
                atomic_place_universals[rhs],
                RelationDirection::LhsOntoRhs,
            );
        }
    }

    let mut re_tcx = RegionTyCheckCx {
        ccx: &mut ccx,
        place_numbering: &place_numbering,
        env,
        atomic_place_universals: &atomic_place_universals,
        imported_locals: &imported_locals,
        body: &body,
    };

    // FIXME: more fine-grained
    for (local_idx, local_ty) in body.locals.indices().zip(&imported_locals) {
        for atomic in place_numbering
            .lookup_range(s, MirPlace::new(tcx, local_idx, []))
            .iter_newtyped()
        {
            re_tcx
                .ccx
                .oblige_ty_outlives_re(
                    *local_ty,
                    atomic_place_universals[atomic],
                    RelationDirection::LhsOntoRhs,
                )
                .report_never();
        }
    }

    // TODO: This is currently needed because the obligations above don't run in order.
    re_tcx.ccx.poll_obligations();

    re_tcx.check_body();

    ccx.verify();
}

struct RegionTyCheckCx<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    place_numbering: &'a PlaceNumbering,
    env: ClauseImportEnv,
    atomic_place_universals: &'a IndexVec<AtomicPlaceIdx, Re>,
    imported_locals: &'a IndexVec<MirLocalIdx, Ty>,
    body: &'a MirBody,
}

impl<'a, 'tcx> RegionTyCheckCx<'a, 'tcx> {
    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn session(&self) -> &'tcx Session {
        self.ccx.session()
    }

    fn check_body(&mut self) {
        for block in self.body.blocks() {
            for stmt in block.stmts(MirBodyDirection::Forwards) {
                match stmt.kind() {
                    MirStmtKind::StorageLive(_) | MirStmtKind::StorageDead(_) => {
                        // (trivially type-checked)
                    }
                    MirStmtKind::Assign(assign) => {
                        let (lhs, rhs) = &**assign;
                        let lhs = self.check_place(*lhs);
                        self.check_assign(stmt.stmt().source_info, lhs, rhs);
                    }
                    MirStmtKind::Discard(discard) => {
                        let (lhs, rhs) = &**discard;
                        let lhs = self.ccx.import_elsewhere(&self.env, *lhs);
                        self.check_assign(stmt.stmt().source_info, lhs, rhs);
                    }
                }
            }

            match block.terminator_kind() {
                MirTerminatorKind::Goto(_)
                | MirTerminatorKind::Unreachable
                | MirTerminatorKind::Return
                | MirTerminatorKind::UnwindResume
                | MirTerminatorKind::SwitchInt {
                    discr: _,
                    constants: _,
                    targets: _,
                }
                | MirTerminatorKind::EnsureDropped {
                    place: _,
                    target: _,
                    unwind: _,
                } => {
                    // (trivially type-checked or doesn't affect region checking)
                }
                MirTerminatorKind::Call {
                    callee,
                    args,
                    destination,
                    target: _,
                    unwind: _,
                } => {
                    // TODO
                }
            }
        }
    }

    fn check_place(&mut self, place: MirPlace) -> Ty {
        let s = self.session();

        let mut ty = self.imported_locals[place.local];

        for proj in place.projections.r(s) {
            ty = match proj {
                MirPlaceElem::DerefPtr => {
                    let TyKind::Reference(_lt, _muta, pointee) = *ty.r(s) else {
                        unreachable!()
                    };

                    pointee
                }
                MirPlaceElem::Field(ResolvedFieldIdx::Tuple {
                    field_idx,
                    max_elems: _,
                }) => {
                    let TyKind::Tuple(elems) = *ty.r(s) else {
                        unreachable!()
                    };

                    elems.r(s)[*field_idx as usize]
                }
                MirPlaceElem::Field(ResolvedFieldIdx::Adt(ctor, field_idx)) => {
                    let TyKind::Adt(AdtInstance { def, params }) = *ty.r(s) else {
                        unreachable!()
                    };

                    let adt_env = ClauseImportEnv::new(
                        Some(ty),
                        [GenericSubst::new(def.r(s).generics, params)],
                    );

                    let ty = *ctor.r(s).fields[*field_idx].ty;
                    self.ccx.import_elsewhere(&adt_env, ty)
                }
            }
        }

        ty
    }

    fn check_assign(&mut self, source_info: MirSourceInfo, lhs: Ty, rvalue: &MirRvalue) {
        let s = self.session();
        let tcx = self.tcx();

        match rvalue {
            MirRvalue::UnreachablePlaceholder => {
                unreachable!()
            }
            MirRvalue::Tuple(operands) => {
                let rhs = tcx.intern(TyKind::Tuple(
                    tcx.intern_list(
                        &operands
                            .iter()
                            .map(|op| self.check_place(op.place()))
                            .collect::<Vec<_>>(),
                    ),
                ));

                self.check_assign_types(source_info, lhs, rhs);
            }
            MirRvalue::Adt(ctor, operands) => {
                let TyKind::Adt(AdtInstance { def, params }) = *lhs.r(s) else {
                    unreachable!(
                        "expected ADT, got {}",
                        self.ccx.pretty(ClausePrettyFmtOpts::default()).wrap(lhs)
                    );
                };
                assert_eq!(def, ctor.r(s).owner.item(s));

                let adt_env =
                    ClauseImportEnv::new(Some(lhs), [GenericSubst::new(def.r(s).generics, params)]);

                for (field, operand) in ctor.r(s).fields.iter().zip(operands) {
                    let lhs = self.ccx.import_elsewhere(&adt_env, *field.ty);
                    let rhs = self.check_place(operand.place());

                    self.check_assign_types(source_info, lhs, rhs);
                }
            }
            MirRvalue::Use(operand) => {
                let rhs = self.check_place(operand.place());
                self.check_assign_types(source_info, lhs, rhs);
            }
            MirRvalue::MoveOutRef {
                can_move_from: _,
                ref_place,
            } => {
                let ref_place = self.check_place(*ref_place);

                let TyKind::Reference(_lt, _muta, pointee) = *ref_place.r(s) else {
                    unreachable!()
                };

                self.check_assign_types(source_info, lhs, pointee);
            }
            MirRvalue::Ref(mutability, pointee) => {
                let pointee_ty = self.check_place(*pointee);

                let ref_lt = if let Some(last_deref) = pointee
                    .projections
                    .r(s)
                    .iter()
                    .rposition(|elem| matches!(elem, MirPlaceElem::DerefPtr))
                {
                    // If `pointee` is a pointer dereference, use the lifetime of the dereferenced
                    // reference.

                    let TyKind::Reference(ref_lt, _, _) = *self
                        .check_place(pointee.truncate_to_len(tcx, last_deref))
                        .r(s)
                    else {
                        unreachable!()
                    };

                    ref_lt
                } else {
                    // If `pointee` is a local, take the closure of its referenced places.

                    let ref_lt = self.ccx.fresh_re_infer();

                    for atomic_place in self
                        .place_numbering
                        .lookup_range(s, *pointee)
                        .iter_newtyped()
                    {
                        let atomic_universal = self.atomic_place_universals[atomic_place];

                        self.ccx
                            .ucx_mut()
                            .unify_re_and_re(atomic_universal, ref_lt, RelationMode::LhsOntoRhs)
                            .report_never();
                    }

                    ref_lt
                };

                let rhs = tcx.intern(TyKind::Reference(ref_lt, *mutability, pointee_ty));
                self.check_assign_types(source_info, lhs, rhs);
            }
            MirRvalue::Zst(ty) | MirRvalue::Literal(ty, _) => {
                let rhs = self.ccx.import_elsewhere(&self.env, *ty);
                self.check_assign_types(source_info, lhs, rhs);
            }
            MirRvalue::BinaryOp(kind, ops) => {
                let (bin_lhs, _bin_rhs) = **ops;
                let bin_lhs = self.check_place(bin_lhs.place());

                let rhs = match kind {
                    MirStraightBinOpKind::Add
                    | MirStraightBinOpKind::Sub
                    | MirStraightBinOpKind::Mul
                    | MirStraightBinOpKind::Div
                    | MirStraightBinOpKind::Rem
                    | MirStraightBinOpKind::BitXor
                    | MirStraightBinOpKind::BitAnd
                    | MirStraightBinOpKind::BitOr
                    | MirStraightBinOpKind::Shl
                    | MirStraightBinOpKind::Shr => bin_lhs,
                    MirStraightBinOpKind::Eq
                    | MirStraightBinOpKind::Lt
                    | MirStraightBinOpKind::Le
                    | MirStraightBinOpKind::Ne
                    | MirStraightBinOpKind::Ge
                    | MirStraightBinOpKind::Gt => tcx.intern(TyKind::Simple(SimpleTyKind::Bool)),
                };

                self.check_assign_types(source_info, lhs, rhs);
            }
            MirRvalue::UnaryOp(kind, op) => {
                let op = self.check_place(op.place());

                let rhs = match kind {
                    MirStraightUnOpKind::Not | MirStraightUnOpKind::Neg => op,
                };

                self.check_assign_types(source_info, lhs, rhs);
            }
            MirRvalue::Discriminant(mir_place) => todo!(),
            MirRvalue::DynUse(dyn_site_idx, mir_operand) => {
                todo!()
            }
            MirRvalue::Error(_) => {
                // (assumed okay)
            }
        }
    }

    fn check_assign_types(&mut self, source_info: MirSourceInfo, lhs: Ty, rhs: Ty) {
        self.ccx
            .unify_ty_and_ty(lhs, rhs, RelationMode::RhsOntoLhs)
            .unwrap()
            .map(move |_ccx, error| MirSpannedError(source_info, error))
            .report_loud();
    }
}
