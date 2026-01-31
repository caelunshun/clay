use crate::{
    base::{ErrorGuaranteed, Session, arena::HasInterner, syntax::Span},
    semantic::{
        analysis::{
            CheckOrigin, CoherenceMap, FloatingInferVar, ObligationCx, ObligationNotReady,
            RecursionLimitReached, TyAndTyUnifyError, TyCtxt, UnifyCx, UnifyCxMode,
        },
        syntax::{
            InferTyVar, Re, RelationDirection, RelationMode, TraitClause, TraitClauseList,
            TraitSpec, Ty, TyKind, TyOrRe, UniversalReVar, UniversalReVarSourceInfo,
            UniversalTyVar, UniversalTyVarSourceInfo,
        },
    },
};
use index_vec::IndexVec;

const MAX_OBLIGATION_DEPTH: u32 = 256;

#[derive(Debug, Clone)]
pub(super) enum ClauseObligation {
    TyUnifiesTy(CheckOrigin, Ty, Ty, RelationMode),
    TyMeetsTrait(CheckOrigin, Ty, TraitSpec),
    TyOutlivesRe(CheckOrigin, Ty, Re, RelationDirection),
    InferTyWf(Span, InferTyVar),
}

impl ClauseObligation {
    fn verify_depth(&self, ccx: &ClauseCx<'_>) -> Option<ErrorGuaranteed> {
        match self {
            Self::TyUnifiesTy(origin, ..)
            | Self::TyMeetsTrait(origin, ..)
            | Self::TyOutlivesRe(origin, ..) => {
                if origin.depth() > MAX_OBLIGATION_DEPTH {
                    return Some(
                        RecursionLimitReached {
                            origin: origin.clone(),
                        }
                        .emit(ccx),
                    );
                }
            }
            Self::InferTyWf(..) => {
                // (has no depth)
            }
        }

        None
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
    pub(super) universal_vars: IndexVec<UniversalTyVar, UniversalTyVarDescriptor>,
}

#[derive(Clone)]
pub(super) struct UniversalTyVarDescriptor {
    src_info: UniversalTyVarSourceInfo,
    direct_clauses: Option<TraitClauseList>,
    pub(super) elaboration: Option<UniversalElaboration>,
}

#[derive(Debug, Copy, Clone)]
pub struct UniversalElaboration {
    pub clauses: TraitClauseList,
    pub lub_re: Re,
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, coherence: &'tcx CoherenceMap, mode: UnifyCxMode) -> Self {
        Self {
            ocx: ObligationCx::new(tcx, mode),
            coherence,
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

    pub fn ucx(&self) -> &UnifyCx<'tcx> {
        self.ocx.ucx()
    }

    pub fn ucx_mut(&mut self) -> &mut UnifyCx<'tcx> {
        self.ocx.ucx_mut()
    }

    pub fn mode(&self) -> UnifyCxMode {
        self.ucx().mode()
    }

    pub(super) fn push_obligation(&mut self, kind: ClauseObligation) {
        self.ocx.push_obligation(kind);
        self.process_obligations();
    }

    fn process_obligations(&mut self) {
        ObligationCx::poll_obligations(
            self,
            |this| &mut this.ocx,
            |this| this.clone(),
            |fork, kind| {
                if let Some(_err) = kind.verify_depth(fork) {
                    return Ok(());
                }

                match kind {
                    ClauseObligation::TyUnifiesTy(origin, lhs, rhs, mode) => {
                        if let Err(err) = fork.ucx_mut().unify_ty_and_ty(&origin, lhs, rhs, mode) {
                            err.emit(fork);
                        }

                        Ok(())
                    }
                    ClauseObligation::TyMeetsTrait(origin, lhs, rhs) => {
                        match fork.try_oblige_ty_meets_trait(&origin, lhs, rhs) {
                            Ok(Ok(())) => Ok(()),
                            Ok(Err(err)) => {
                                err.emit(fork);
                                Ok(())
                            }
                            Err(ObligationNotReady) => Err(ObligationNotReady),
                        }
                    }
                    ClauseObligation::TyOutlivesRe(origin, lhs, rhs, dir) => {
                        fork.run_oblige_ty_outlives_re(&origin, lhs, rhs, dir)
                    }
                    ClauseObligation::InferTyWf(span, var) => {
                        fork.run_oblige_infer_ty_wf(span, var)
                    }
                }
            },
        );
    }

    pub fn suppress_obligation_eval<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let was_suppressed = self.ocx.obligation_eval_suppressed();
        self.ocx.set_obligation_eval_suppressed(true);

        let mut this = scopeguard::guard(self, |this| {
            this.ocx.set_obligation_eval_suppressed(was_suppressed)
        });

        f(&mut this)
    }

    pub fn try_fork<T, E>(&mut self, f: impl FnOnce(&mut Self) -> Result<T, E>) -> Result<T, E> {
        self.suppress_obligation_eval(|this| {
            let mut fork = this.clone();

            let res = f(&mut fork);

            if res.is_ok() {
                *this = fork;
            }

            res
        })
    }
}

// Basic operations
impl<'tcx> ClauseCx<'tcx> {
    pub fn fresh_ty_infer_var(&mut self) -> InferTyVar {
        self.ucx_mut().fresh_ty_infer_var()
    }

    pub fn fresh_ty_infer(&mut self) -> Ty {
        self.ucx_mut().fresh_ty_infer()
    }

    pub fn lookup_ty_infer_var(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        self.ucx().lookup_ty_infer_var(var)
    }

    pub fn peel_ty_infer_var(&self, ty: Ty) -> Ty {
        self.ucx().peel_ty_infer_var(ty)
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

    pub fn fresh_ty_universal_var(&mut self, src_info: UniversalTyVarSourceInfo) -> UniversalTyVar {
        self.universal_vars.push(UniversalTyVarDescriptor {
            src_info,
            direct_clauses: None,
            elaboration: None,
        })
    }

    pub fn fresh_ty_universal(&mut self, src_info: UniversalTyVarSourceInfo) -> Ty {
        self.tcx()
            .intern(TyKind::UniversalVar(self.fresh_ty_universal_var(src_info)))
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

    pub fn direct_ty_universal_clauses(&self, var: UniversalTyVar) -> TraitClauseList {
        self.universal_vars[var].direct_clauses.unwrap()
    }

    pub fn lookup_universal_ty_src_info(
        &mut self,
        var: UniversalTyVar,
    ) -> UniversalTyVarSourceInfo {
        self.universal_vars[var].src_info
    }

    pub fn oblige_re_outlives_re(
        &mut self,
        origin: CheckOrigin,
        lhs: Re,
        rhs: Re,
        mode: RelationMode,
    ) {
        self.ucx_mut().unify_re_and_re(&origin, lhs, rhs, mode);
    }

    pub fn oblige_ty_unifies_ty(
        &mut self,
        origin: CheckOrigin,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) {
        self.push_obligation(ClauseObligation::TyUnifiesTy(origin, lhs, rhs, mode));
    }

    pub fn unify_ty_and_ty(
        &mut self,
        origin: &CheckOrigin,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) -> Result<(), Box<TyAndTyUnifyError>> {
        self.ucx_mut().unify_ty_and_ty(origin, lhs, rhs, mode)
    }

    pub fn oblige_re_meets_clauses(&mut self, origin: &CheckOrigin, lhs: Re, rhs: TraitClauseList) {
        let s = self.session();

        for &clause in rhs.r(s) {
            match clause {
                TraitClause::Outlives(dir, rhs) => {
                    self.oblige_general_outlives(origin.clone(), TyOrRe::Re(lhs), rhs, dir);
                }
                TraitClause::Trait(_) => {
                    unreachable!()
                }
            }
        }
    }

    pub fn verify(&self) {
        self.ucx().verify(self);
    }
}
