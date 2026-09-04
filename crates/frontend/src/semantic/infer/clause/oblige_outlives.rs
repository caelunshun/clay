//! Logic to implement the outlives obligation.

use crate::semantic::{
    infer::{
        ClauseCx, ClauseObligation, GeneralOutlivesError, MultiPromiseBuilder, ObligationNotReady,
        ObligationResult, ObligationTermination, Promise, PromiseHandle, TyOutlivesReError,
        TyOutlivesReErrorCulprit, TyOutlivesTyError,
    },
    syntax::{Re, RelationDirection, RelationMode, SimpleTySet, Ty, TyKind, TyOrRe},
};

impl<'tcx> ClauseCx<'tcx> {
    pub fn permit_universe_re_outlives_general(
        &mut self,
        universal: Re,
        other: TyOrRe,
        dir: RelationDirection,
    ) {
        match other {
            TyOrRe::Re(other) => {
                self.permit_universe_re_outlives_re(universal, other, dir);
            }
            TyOrRe::Ty(other) => {
                self.permit_universe_re_outlives_ty(universal, other, dir);
            }
        }
    }

    pub fn permit_universe_re_outlives_ty(
        &mut self,
        universal: Re,
        other: Ty,
        dir: RelationDirection,
    ) {
        // Without loss of generality...
        //
        // If `dir == LhsOntoRhs`...
        //
        // ```
        // universal: 'a
        // 'a: other
        // =>
        // universal: other
        // ```
        //
        // If `dir == RhsOntoLhs`...
        //
        // ```
        // 'a: universal
        // other: 'a
        // =>
        // other: universal
        // ```

        let joiner = self.fresh_re_infer();

        // `'a: other` (inverse: `other: 'a`)
        self.oblige_ty_outlives_re(other, joiner, dir.invert())
            .report_never();

        // `universal: 'a` (inverse: `'a: universal`)
        self.permit_universe_re_outlives_re(universal, joiner, dir);
    }

    pub fn oblige_general_outlives(
        &mut self,
        lhs: TyOrRe,
        rhs: TyOrRe,
        dir: RelationDirection,
    ) -> Promise<'tcx, GeneralOutlivesError> {
        let (lhs, rhs) = dir.adapt(lhs, rhs);

        match (lhs, rhs) {
            (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => self
                .oblige_re_outlives_re(lhs, rhs, RelationMode::LhsOntoRhs)
                .map(|_ccx, err| err.into()),
            (TyOrRe::Ty(lhs), TyOrRe::Re(rhs)) => self
                .oblige_ty_outlives_re(lhs, rhs, RelationDirection::LhsOntoRhs)
                .map(|_ccx, err| err.into()),
            (TyOrRe::Re(lhs), TyOrRe::Ty(rhs)) => self
                .oblige_ty_outlives_re(rhs, lhs, RelationDirection::RhsOntoLhs)
                .map(|_ccx, err| err.into()),
            (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => self
                .oblige_ty_outlives_ty(lhs, rhs)
                .map(|_ccx, err| err.into()),
        }
    }

    pub fn oblige_ty_outlives_ty(&mut self, lhs: Ty, rhs: Ty) -> Promise<'tcx, TyOutlivesTyError> {
        // LHS: 'a
        // 'a: RHS
        // => LHS: RHS

        let joiner = self.fresh_re_infer();

        // LHS: 'a
        self.oblige_ty_outlives_re(lhs, joiner, RelationDirection::LhsOntoRhs)
            // Any errors would be introduced in the second obligation.
            .report_never();

        // 'a: RHS
        self.oblige_ty_outlives_re(rhs, joiner, RelationDirection::RhsOntoLhs)
            .map(move |_ccx, error| TyOutlivesTyError {
                lhs,
                rhs,
                joiner,
                errors: error.errors,
            })
    }

    pub fn oblige_ty_outlives_re(
        &mut self,
        lhs: Ty,
        rhs: Re,
        dir: RelationDirection,
    ) -> Promise<'tcx, TyOutlivesReError> {
        let (promise, handle) = Promise::new();

        self.push_obligation(ClauseObligation::TyOutlivesRe {
            handle,
            lhs,
            rhs,
            dir,
        });

        promise
    }

    pub(super) fn run_oblige_ty_outlives_re(
        &mut self,
        handle: PromiseHandle<'tcx, TyOutlivesReError>,
        lhs: Ty,
        rhs: Re,
        dir: RelationDirection,
    ) -> ObligationResult {
        let s = self.session();

        let mut collector = MultiPromiseBuilder::new();

        match *lhs.r(s) {
            TyKind::HrtbVar(_) | TyKind::HrtbProjection(_) => {
                unreachable!()
            }
            TyKind::Simple(_) | TyKind::Error(_) | TyKind::FnDef(_) => {
                // (trivial)
            }
            TyKind::Reference(lhs, _muta, _pointee) => {
                self.ucx_mut()
                    .unify_re_and_re(lhs, rhs, dir.to_mode())
                    .map(|_ccx, error| TyOutlivesReErrorCulprit::Regular(error))
                    .join(&mut collector);
            }
            TyKind::Adt(lhs) => {
                // ADTs are bounded by the regions which they mention.
                for &lhs in lhs.params.r(s) {
                    match lhs {
                        TyOrRe::Re(lhs) => {
                            self.ucx_mut()
                                .unify_re_and_re(lhs, rhs, dir.to_mode())
                                .map(|_ccx, error| TyOutlivesReErrorCulprit::Regular(error))
                                .join(&mut collector);
                        }
                        TyOrRe::Ty(lhs) => {
                            self.oblige_ty_outlives_re(lhs, rhs, dir)
                                .map(|_ccx, error| error.errors)
                                .flat_join(&mut collector);
                        }
                    }
                }
            }

            TyKind::Trait(lhs_re, _muta, _lhs_spec) => {
                self.ucx_mut()
                    .unify_re_and_re(lhs_re, rhs, dir.to_mode())
                    .map(|_ccx, error| TyOutlivesReErrorCulprit::Regular(error))
                    .join(&mut collector);
            }
            TyKind::Tuple(lhs) => {
                for &lhs in lhs.r(s) {
                    self.oblige_ty_outlives_re(lhs, rhs, dir)
                        .map(|_ccx, error| error.errors)
                        .flat_join(&mut collector);
                }
            }
            TyKind::Universal(universal) => {
                let lub_re = self
                    .elaborate_ty_universal_clauses_possibly_floating(universal)
                    .lub_re;

                self.oblige_re_outlives_re(lub_re, rhs, dir.to_mode())
                    .map(|_ccx, error| TyOutlivesReErrorCulprit::Regular(error))
                    .join(&mut collector);
            }
            TyKind::InferVar(inf_lhs) => {
                match self.ucx().lookup_ty_infer_var(inf_lhs) {
                    Ok(inf_lhs) => {
                        self.oblige_ty_outlives_re(inf_lhs, rhs, dir)
                            .map(|_ccx, error| error.errors)
                            .flat_join(&mut collector);
                    }
                    Err(err) => {
                        if err.perm_set.intersects(SimpleTySet::MAYBE_UNIVERSAL) {
                            return Err(ObligationNotReady::UnresolvedInfer(inf_lhs));
                        }

                        // (trivially true of all remaining types)
                    }
                }
            }
        }

        collector
            .finish()
            .map(move |_ccx, errors| TyOutlivesReError { lhs, rhs, errors })
            .forward(self, handle);

        Ok(ObligationTermination::Regular)
    }
}
