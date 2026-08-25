use crate::{
    base::{
        Session,
        arena::{HasInterner, Obj},
    },
    semantic::{
        infer::{
            CoherenceMap, FloatingInferVar, GeneralOutlivesError, HrtbUniverse,
            InstantiatedTraitImplError, MultiPromise, MultiPromiseBuilder, NotCoveredError,
            ObligationNotReady, ObligationResult, Promise, PromiseHandle, PromiseMode,
            ReAndReUnifyError, TyAndSimpleTySetUnifyError, TyAndTyRegionUnifyError,
            TyAndTyStructuralUnifyError, TyAndTyUnifyError, TyAndTyUnifyErrorKind,
            TyOutlivesReError, UnifyCx, UnifyCxMode,
            clause::elaboration::{UniversalElaboration, WipReificationState},
        },
        syntax::{
            Crate, InferTyVar, InferTyVarSourceInfo, Re, RelationDirection, RelationMode,
            SimpleTySet, TraitClause, TraitClauseList, TraitSpec, Ty, TyCtxt, TyKind, TyOrRe,
            UniversalReVar, UniversalReVarSourceInfo, UniversalTyVar, UniversalTyVarSourceInfo,
        },
    },
    utils::hash::FxHashMap,
};
use index_vec::IndexVec;
use std::rc::Rc;

// === Obligation Definitions === //

#[derive(Debug, Clone)]
pub enum ClauseObligation<'tcx> {
    TyUnifiesTy {
        handle: PromiseHandle<'tcx, TyAndTyUnifyError>,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    },
    TyMeetsTrait {
        handle: PromiseHandle<'tcx, InstantiatedTraitImplError>,
        fuel: ClauseFuel,
        universe: HrtbUniverse,
        lhs: Ty,
        rhs: TraitSpec,
    },
    TyOutlivesRe {
        handle: PromiseHandle<'tcx, TyOutlivesReError>,
        lhs: Ty,
        rhs: Re,
        dir: RelationDirection,
    },
    UnifyReifiedElaboratedClauses {
        root: UniversalTyVar,
        clauses: TraitClauseList,
        reified_vars: WipReificationState,
    },
    Covered {
        handle: PromiseHandle<'tcx, NotCoveredError>,
        must_mention: Rc<FxHashMap<UniversalTyVar, u32>>,
        in_type: Option<Ty>,
        in_trait: Option<TraitSpec>,
    },
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ClauseFuelKillId(u32);

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ClauseFuel {
    remaining: u32,
    kill_id: ClauseFuelKillId,
}

impl ClauseFuel {
    pub fn new(remaining: u32, kill_id: ClauseFuelKillId) -> Self {
        Self { remaining, kill_id }
    }

    pub fn consume(self) -> Self {
        Self {
            remaining: self.remaining.saturating_sub(1),
            kill_id: self.kill_id,
        }
    }

    pub fn is_exhausted(self) -> bool {
        self.remaining == 0
    }

    pub fn remaining(self) -> u32 {
        self.remaining
    }

    pub fn kill_id(self) -> ClauseFuelKillId {
        self.kill_id
    }
}

// === ClauseCx Definition === //

/// A type inference context for solving type obligations of the form...
///
/// - `Region: Region`
/// - `Type = Type`
/// - `Type: Clauses`
/// - `well-formed Type`
///
/// Obligations are enqueued out of order and the context solves them as inference variables arrive.
///
/// This context is built on top of an [`ObligationCx`].
///
/// ## Multi-Pass Checking
///
/// This context has two modes: region unaware and region aware.
///
/// - The region unaware mode just solves for type equalities, making it ideal for a first pass of
///   type-checker where one just wants to solve for type inference variables. This process is
///   allowed to fail.
///
/// - The region aware mode can take the solved inference types and, after replacing all the erased
///   regions within those solved inference types with fresh region inference variables, it can run
///   a second pass of type-checking to ensure that region inference is correct.
///
/// If all the types checked with a region aware check were obtained by a prior region unaware
/// type-check, the inference methods will never return type errors—only region errors.
///
/// This two-pass design is necessary because we want each inferred expression type to have its own
/// set of fresh region inference variables. If we instead tried to do type solving in a single
/// pass, we'd either have to...
///
/// a) Wait until a source expression's type is fully solved so that we can replace all its regions
///    with fresh region variables, which could prevent us from properly inferring certain patterns.
///
/// b) Equate source expression types without instantiating fresh new inference variable for each of
///    them, preventing us from handling region-based sub-typing. This is what using a region-aware
///    mode for the first inference pass would accomplish.
///
/// Note that, if there are no type inference variables involved in your seed queries (e.g. when
/// WF-checking traits), you can immediately skip to region aware checking.
#[derive(Clone)]
pub struct ClauseCx<'tcx> {
    ucx: UnifyCx<'tcx>,
    pending_obligations: Vec<ClauseObligationState<'tcx>>,
    coherence: &'tcx CoherenceMap,
    krate: Obj<Crate>,
    promise_mode: PromiseMode,
    fuel_kill_gen: ClauseFuelKillId,
    pub(super) universal_vars: IndexVec<UniversalTyVar, UniversalTyVarDescriptor>,
}

#[derive(Clone)]
struct ClauseObligationState<'tcx> {
    kind: ClauseObligation<'tcx>,
    not_ready: Option<ObligationNotReady>,
}

#[derive(Clone)]
pub(super) struct UniversalTyVarDescriptor {
    direct_clauses: Option<TraitClauseList>,
    pub(super) elaboration: Option<UniversalElaboration>,
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn new(
        tcx: &'tcx TyCtxt,
        coherence: &'tcx CoherenceMap,
        krate: Obj<Crate>,
        mode: UnifyCxMode,
    ) -> Self {
        Self {
            ucx: UnifyCx::new(tcx, mode),
            pending_obligations: Vec::new(),
            coherence,
            krate,
            promise_mode: PromiseMode::RootContext,
            fuel_kill_gen: ClauseFuelKillId(0),
            universal_vars: IndexVec::new(),
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.ucx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.ucx.session()
    }

    pub fn coherence(&self) -> &'tcx CoherenceMap {
        self.coherence
    }

    pub fn krate(&self) -> Obj<Crate> {
        self.krate
    }

    pub fn ucx(&self) -> &UnifyCx<'tcx> {
        &self.ucx
    }

    pub fn ucx_mut(&mut self) -> &mut UnifyCx<'tcx> {
        &mut self.ucx
    }

    pub fn promise_mode(&self) -> PromiseMode {
        self.promise_mode
    }

    pub fn is_silent(&self) -> bool {
        !self.promise_mode.is_root()
    }

    pub fn make_silent(&mut self) {
        self.promise_mode = PromiseMode::ProbeContext;
    }

    pub fn with_silent(mut self) -> Self {
        self.make_silent();
        self
    }

    pub fn mode(&self) -> UnifyCxMode {
        self.ucx().mode()
    }
}

// === Obligation Runner === //

impl<'tcx> ClauseCx<'tcx> {
    pub(super) fn push_obligation(&mut self, kind: ClauseObligation<'tcx>) {
        self.pending_obligations.push(ClauseObligationState {
            kind,
            not_ready: None,
        });
    }

    pub fn poll_obligations(&mut self) {
        loop {
            let mut made_progress = false;

            // Process all obligations back to front.
            let mut curr_idx = self.pending_obligations.len();

            while curr_idx > 0 {
                curr_idx -= 1;

                let kind = self.pending_obligations[curr_idx].kind.clone();

                let mut fork = self.clone();

                let res = match kind {
                    ClauseObligation::TyUnifiesTy {
                        handle,
                        lhs,
                        rhs,
                        mode,
                    } => fork.run_oblige_ty_unifies_ty(handle, lhs, rhs, mode),
                    ClauseObligation::TyMeetsTrait {
                        handle,
                        fuel,
                        universe,
                        lhs,
                        rhs,
                    } => fork
                        .run_oblige_ty_meets_trait_instantiated(handle, fuel, universe, lhs, rhs),
                    ClauseObligation::TyOutlivesRe {
                        handle,
                        lhs,
                        rhs,
                        dir: direction,
                    } => fork.run_oblige_ty_outlives_re(handle, lhs, rhs, direction),
                    ClauseObligation::UnifyReifiedElaboratedClauses {
                        root,
                        clauses,
                        reified_vars,
                    } => fork.oblige_unify_reified_elaborated_clauses(root, clauses, reified_vars),
                    ClauseObligation::Covered {
                        handle,
                        must_mention,
                        in_type,
                        in_trait,
                    } => fork.run_oblige_covered(handle, must_mention, in_type, in_trait),
                };

                // If we finished processing the obligation, remove it from the queue and mark
                // progress so we can continue processing.
                match res {
                    Ok(()) => {
                        *self = fork;
                        self.pending_obligations.swap_remove(curr_idx);
                        made_progress = true;
                        // (forces depth-first expansion)
                        break;
                    }
                    Err(err) => {
                        self.pending_obligations[curr_idx].not_ready = Some(err);
                    }
                }
            }

            if !made_progress {
                break;
            }
        }
    }

    pub(super) fn kill_obligations_with_id(&mut self, kill_id: ClauseFuelKillId) {
        self.pending_obligations.retain(|obligation| {
            let other_kill_id = match obligation.kind {
                ClauseObligation::TyUnifiesTy { .. }
                | ClauseObligation::TyOutlivesRe { .. }
                | ClauseObligation::UnifyReifiedElaboratedClauses { .. }
                | ClauseObligation::Covered { .. } => None,
                ClauseObligation::TyMeetsTrait { fuel, .. } => Some(fuel.kill_id()),
            };

            Some(kill_id) != other_kill_id
        });
    }
}

// === Basic operations === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn fresh_clause_fuel(&mut self) -> ClauseFuel {
        let kill_id = self.fuel_kill_gen;

        self.fuel_kill_gen = ClauseFuelKillId(
            self.fuel_kill_gen
                .0
                .checked_add(1)
                .expect("too many clause fuel generations created"),
        );

        ClauseFuel {
            remaining: 64,
            kill_id,
        }
    }

    pub fn fresh_ty_infer_var_restricted(
        &mut self,
        max_universe: HrtbUniverse,
        source_info: InferTyVarSourceInfo,
        perm_set: SimpleTySet,
    ) -> InferTyVar {
        self.ucx_mut()
            .fresh_ty_infer_var(max_universe, source_info, perm_set)
    }

    pub fn fresh_ty_infer_restricted(
        &mut self,
        max_universe: HrtbUniverse,
        source_info: InferTyVarSourceInfo,
        perm_set: SimpleTySet,
    ) -> Ty {
        self.tcx()
            .intern(TyKind::InferVar(self.fresh_ty_infer_var_restricted(
                max_universe,
                source_info,
                perm_set,
            )))
    }

    pub fn fresh_ty_infer_var(
        &mut self,
        max_universe: HrtbUniverse,
        source_info: InferTyVarSourceInfo,
    ) -> InferTyVar {
        self.fresh_ty_infer_var_restricted(max_universe, source_info, SimpleTySet::all())
    }

    pub fn fresh_ty_infer(
        &mut self,
        max_universe: HrtbUniverse,
        source_info: InferTyVarSourceInfo,
    ) -> Ty {
        self.fresh_ty_infer_restricted(max_universe, source_info, SimpleTySet::all())
    }

    pub fn next_ty_infer_var(&self) -> InferTyVar {
        self.ucx().next_ty_infer_var()
    }

    pub fn lookup_ty_infer_var_without_poll(
        &self,
        var: InferTyVar,
    ) -> Result<Ty, FloatingInferVar<'_>> {
        self.ucx().lookup_ty_infer_var(var)
    }

    pub fn force_update_permissions_of_ty_var(&mut self, var: InferTyVar, perms: SimpleTySet) {
        self.ucx_mut()
            .force_update_permissions_of_ty_var(var, perms);
    }

    pub fn lookup_ty_infer_var_after_poll(
        &mut self,
        var: InferTyVar,
    ) -> Result<Ty, FloatingInferVar<'_>> {
        self.poll_obligations();
        self.lookup_ty_infer_var_without_poll(var)
    }

    pub fn peel_ty_infer_var_without_poll(&self, ty: Ty) -> Ty {
        self.ucx().peel_ty_infer_var(ty)
    }

    pub fn peel_ty_infer_var_after_poll(&mut self, ty: Ty) -> Ty {
        self.poll_obligations();
        self.peel_ty_infer_var_without_poll(ty)
    }

    pub fn fresh_re_infer(&mut self) -> Re {
        self.ucx_mut().fresh_re_infer()
    }

    pub fn fresh_re_universal(&mut self, src_info: UniversalReVarSourceInfo) -> Re {
        self.ucx_mut().fresh_re_universal(src_info)
    }

    pub fn lookup_universal_re_src_info(
        &mut self,
        var: UniversalReVar,
    ) -> UniversalReVarSourceInfo {
        self.ucx_mut().lookup_universal_re_src_info(var)
    }

    pub fn permit_universe_re_outlives_re(
        &mut self,
        universal: Re,
        other: Re,
        dir: RelationDirection,
    ) {
        self.ucx_mut()
            .permit_universe_re_outlives_re(universal, other, dir);
    }

    pub fn fresh_ty_universal_var(
        &mut self,
        in_universe: HrtbUniverse,
        src_info: UniversalTyVarSourceInfo,
    ) -> UniversalTyVar {
        let var = self.ucx_mut().fresh_ty_universal_var(in_universe, src_info);

        let var_parallel = self.universal_vars.push(UniversalTyVarDescriptor {
            direct_clauses: None,
            elaboration: None,
        });

        debug_assert_eq!(var, var_parallel);

        var
    }

    pub fn fresh_ty_universal(
        &mut self,
        in_universe: HrtbUniverse,
        src_info: UniversalTyVarSourceInfo,
    ) -> Ty {
        self.tcx().intern(TyKind::UniversalVar(
            self.fresh_ty_universal_var(in_universe, src_info),
        ))
    }

    pub fn init_any_universal_var_direct_clauses(&mut self, var: TyOrRe, clauses: TraitClauseList) {
        let s = self.session();

        match var {
            TyOrRe::Re(var) => self.init_re_universal_var_direct_clauses(var, clauses),
            TyOrRe::Ty(var) => {
                let TyKind::UniversalVar(var) = *var.r(s) else {
                    unreachable!()
                };

                self.init_ty_universal_var_direct_clauses(var, clauses);
            }
        }
    }

    pub fn init_ty_universal_var_direct_clauses(
        &mut self,
        var: UniversalTyVar,
        clauses: TraitClauseList,
    ) {
        let descriptor = &mut self.universal_vars[var];

        assert!(descriptor.direct_clauses.is_none());
        descriptor.direct_clauses = Some(clauses);
    }

    pub fn init_re_universal_var_direct_clauses(&mut self, var: Re, clauses: TraitClauseList) {
        let s = self.session();

        for clause in clauses.r(s) {
            let TraitClause::Outlives(permitted_outlive_dir, permitted_outlive) = *clause else {
                unreachable!();
            };

            self.permit_universe_re_outlives_general(var, permitted_outlive, permitted_outlive_dir);
        }
    }

    pub fn direct_ty_universal_clauses_possibly_floating(
        &self,
        var: UniversalTyVar,
    ) -> TraitClauseList {
        self.universal_vars[var].direct_clauses.unwrap()
    }

    pub fn lookup_universal_ty_src_info(&self, var: UniversalTyVar) -> UniversalTyVarSourceInfo {
        self.ucx().lookup_universal_ty_src_info(var)
    }

    pub fn lookup_infer_ty_src_info(&self, var: InferTyVar) -> InferTyVarSourceInfo {
        self.ucx().lookup_infer_ty_src_info(var)
    }

    pub fn lookup_universal_ty_hrtb_universe(&self, var: UniversalTyVar) -> &HrtbUniverse {
        self.ucx().lookup_universal_ty_hrtb_universe(var)
    }

    pub fn oblige_re_outlives_re(
        &mut self,
        lhs: Re,
        rhs: Re,
        mode: RelationMode,
    ) -> Promise<'tcx, ReAndReUnifyError> {
        self.ucx_mut().unify_re_and_re(lhs, rhs, mode)
    }

    pub fn oblige_ty_unifies_ty(
        &mut self,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) -> Promise<'tcx, TyAndTyUnifyError> {
        let (promise, handle) = Promise::new();

        self.push_obligation(ClauseObligation::TyUnifiesTy {
            handle,
            lhs,
            rhs,
            mode,
        });

        promise
    }

    fn run_oblige_ty_unifies_ty(
        &mut self,
        handle: PromiseHandle<'tcx, TyAndTyUnifyError>,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) -> ObligationResult {
        match self.ucx_mut().unify_ty_and_ty(lhs, rhs, mode) {
            Ok(promise) => {
                promise
                    .map(
                        move |_ccx, TyAndTyRegionUnifyError { regions, .. }| TyAndTyUnifyError {
                            lhs,
                            rhs,
                            mode,
                            kind: TyAndTyUnifyErrorKind::Region(regions),
                        },
                    )
                    .forward(self, handle);
            }
            Err(error) => {
                handle.reject(
                    self,
                    TyAndTyUnifyError {
                        lhs,
                        rhs,
                        mode,
                        kind: TyAndTyUnifyErrorKind::Structural(error.culprits),
                    },
                );
            }
        }

        Ok(())
    }

    pub fn unify_ty_and_ty(
        &mut self,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) -> Result<Promise<'tcx, TyAndTyRegionUnifyError>, Box<TyAndTyStructuralUnifyError>> {
        self.ucx_mut().unify_ty_and_ty(lhs, rhs, mode)
    }

    pub fn unify_ty_and_simple_set(
        &mut self,
        lhs: Ty,
        rhs: SimpleTySet,
    ) -> Result<(), TyAndSimpleTySetUnifyError> {
        self.ucx_mut().unify_ty_and_simple_set(lhs, rhs)
    }

    pub fn oblige_re_meets_clauses(
        &mut self,
        lhs: Re,
        rhs: TraitClauseList,
    ) -> MultiPromise<'tcx, GeneralOutlivesError> {
        let s = self.session();

        let mut collector = MultiPromiseBuilder::new();

        for &clause in rhs.r(s) {
            match clause {
                TraitClause::Outlives(dir, rhs) => {
                    self.oblige_general_outlives(TyOrRe::Re(lhs), rhs, dir)
                        .join(&mut collector);
                }
                TraitClause::Trait(_) => {
                    unreachable!()
                }
            }
        }

        collector.finish()
    }

    pub fn verify(&mut self) {
        self.poll_obligations();

        for state in &self.pending_obligations {
            ObligationUnfulfilled {
                obligation: state.kind.clone(),
                reason: state.not_ready.clone().unwrap(),
            }
            .report(self);
        }

        self.ucx().verify(self);
    }
}
