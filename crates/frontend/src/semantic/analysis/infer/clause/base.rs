use crate::{
    base::{
        Session,
        arena::{HasInterner, Obj},
    },
    semantic::{
        analysis::{
            ClauseError, CoherenceMap, FloatingInferVar, HrtbUniverse, ObligationCx,
            ObligationNotReady, ObligationUnfulfilled, ObligeCause, RecursionLimitReached,
            TyAndSimpleTySetUnifyError, TyAndTyUnifyError, UnifyCx, UnifyCxMode,
            infer::clause::elaboration::WipReificationState,
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

const MAX_OBLIGATION_DEPTH: u32 = 256;

#[derive(Debug, Clone)]
pub enum ClauseObligation {
    TyUnifiesTy(ObligeCause, Ty, Ty, RelationMode),
    TyMeetsTrait(ObligeCause, HrtbUniverse, Ty, TraitSpec),
    TyOutlivesRe(ObligeCause, Ty, Re, RelationDirection),
    UnifyReifiedElaboratedClauses(
        ObligeCause,
        UniversalTyVar,
        TraitClauseList,
        WipReificationState,
    ),
    Covered(
        ObligeCause,
        Rc<FxHashMap<UniversalTyVar, u32>>,
        Option<Ty>,
        Option<TraitSpec>,
    ),
}

impl ClauseObligation {
    pub fn cause(&self) -> &ObligeCause {
        let (Self::TyUnifiesTy(cause, ..)
        | Self::TyMeetsTrait(cause, ..)
        | Self::TyOutlivesRe(cause, ..)
        | Self::UnifyReifiedElaboratedClauses(cause, ..)
        | Self::Covered(cause, ..)) = self;

        cause
    }
}

// === ClauseCx Core === //

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
    ocx: ObligationCx<'tcx, ClauseObligation>,
    coherence: &'tcx CoherenceMap,
    krate: Obj<Crate>,
    is_silent: bool,
    pub(super) universal_vars: IndexVec<UniversalTyVar, UniversalTyVarDescriptor>,
}

#[derive(Clone)]
pub(super) struct UniversalTyVarDescriptor {
    direct_clauses: Option<TraitClauseList>,
    pub(super) elaboration: Option<UniversalElaboration>,
}

#[derive(Debug, Clone)]
pub struct UniversalElaboration {
    pub clauses: TraitClauseList,
    pub lub_re: Re,
    pub wip_reification_state: Option<WipReificationState>,
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn new(
        tcx: &'tcx TyCtxt,
        coherence: &'tcx CoherenceMap,
        krate: Obj<Crate>,
        mode: UnifyCxMode,
    ) -> Self {
        Self {
            ocx: ObligationCx::new(tcx, mode),
            coherence,
            krate,
            is_silent: false,
            universal_vars: IndexVec::new(),
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.ocx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.ocx.session()
    }

    pub fn coherence(&self) -> &'tcx CoherenceMap {
        self.coherence
    }

    pub fn krate(&self) -> Obj<Crate> {
        self.krate
    }

    pub fn ucx(&self) -> &UnifyCx<'tcx> {
        self.ocx.ucx()
    }

    pub fn ucx_mut(&mut self) -> &mut UnifyCx<'tcx> {
        self.ocx.ucx_mut()
    }

    pub fn is_silent(&self) -> bool {
        self.is_silent
    }

    pub fn make_silent(&mut self) {
        self.is_silent = true;
    }

    pub fn with_silent(mut self) -> Self {
        self.make_silent();
        self
    }

    pub fn mode(&self) -> UnifyCxMode {
        self.ucx().mode()
    }

    pub(super) fn push_obligation(&mut self, kind: ClauseObligation) {
        self.ocx.push_obligation(kind);
    }

    pub fn poll_obligations(&mut self) {
        ObligationCx::poll_obligations(
            self,
            |this| &mut this.ocx,
            |this| this.clone(),
            |fork, kind| {
                if kind.cause().depth() > MAX_OBLIGATION_DEPTH {
                    RecursionLimitReached {
                        cause: kind.cause().clone(),
                    }
                    .report(fork);

                    return Ok(());
                }

                match kind {
                    ClauseObligation::TyUnifiesTy(cause, lhs, rhs, mode) => {
                        if let Err(err) = fork.ucx_mut().unify_ty_and_ty(&cause, lhs, rhs, mode) {
                            ClauseError::from(*err).report(fork);
                        }

                        Ok(())
                    }
                    ClauseObligation::TyMeetsTrait(cause, universe, lhs, rhs) => {
                        match fork
                            .run_oblige_ty_meets_trait_instantiated(&cause, universe, lhs, rhs)
                        {
                            Ok(Ok(())) => Ok(()),
                            Ok(Err(err)) => {
                                err.report(fork);
                                Ok(())
                            }
                            Err(ObligationNotReady) => Err(ObligationNotReady),
                        }
                    }
                    ClauseObligation::TyOutlivesRe(cause, lhs, rhs, dir) => {
                        fork.run_oblige_ty_outlives_re(&cause, lhs, rhs, dir)
                    }
                    ClauseObligation::UnifyReifiedElaboratedClauses(
                        cause,
                        root,
                        clauses,
                        reified_vars,
                    ) => fork.oblige_unify_reified_elaborated_clauses(
                        &cause,
                        root,
                        clauses,
                        reified_vars,
                    ),
                    ClauseObligation::Covered(cause, must_mention, in_type, in_trait) => {
                        fork.run_oblige_covered(cause, must_mention, in_type, in_trait)
                    }
                }
            },
        );
    }
}

// Basic operations
impl<'tcx> ClauseCx<'tcx> {
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

    pub fn init_ty_universal_var_direct_clauses(
        &mut self,
        var: UniversalTyVar,
        clauses: TraitClauseList,
    ) {
        let descriptor = &mut self.universal_vars[var];

        assert!(descriptor.direct_clauses.is_none());
        descriptor.direct_clauses = Some(clauses);
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
        cause: ObligeCause,
        lhs: Re,
        rhs: Re,
        mode: RelationMode,
    ) {
        self.ucx_mut().unify_re_and_re(&cause, lhs, rhs, mode);
    }

    pub fn oblige_ty_unifies_ty(
        &mut self,
        cause: ObligeCause,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) {
        self.push_obligation(ClauseObligation::TyUnifiesTy(cause, lhs, rhs, mode));
    }

    pub fn unify_ty_and_ty(
        &mut self,
        cause: &ObligeCause,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) -> Result<(), Box<TyAndTyUnifyError>> {
        self.ucx_mut().unify_ty_and_ty(cause, lhs, rhs, mode)
    }

    pub fn unify_ty_and_simple_set(
        &mut self,
        cause: &ObligeCause,
        lhs: Ty,
        rhs: SimpleTySet,
    ) -> Result<(), TyAndSimpleTySetUnifyError> {
        self.ucx_mut().unify_ty_and_simple_set(cause, lhs, rhs)
    }

    pub fn oblige_re_meets_clauses(&mut self, cause: &ObligeCause, lhs: Re, rhs: TraitClauseList) {
        let s = self.session();

        for &clause in rhs.r(s) {
            match clause {
                TraitClause::Outlives(dir, rhs) => {
                    self.oblige_general_outlives(cause.clone(), TyOrRe::Re(lhs), rhs, dir);
                }
                TraitClause::Trait(_) => {
                    unreachable!()
                }
            }
        }
    }

    pub fn verify(&mut self) {
        self.poll_obligations();

        for obligation in self.ocx.pending_obligations().to_vec() {
            ObligationUnfulfilled {
                obligation: obligation.clone(),
            }
            .report(self);
        }

        self.ucx().verify(self);
    }
}
