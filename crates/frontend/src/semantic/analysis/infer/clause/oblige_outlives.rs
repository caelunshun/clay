//! Logic to implement the outlives obligation.

use crate::semantic::{
    analysis::{
        ClauseCx, ClauseOrigin, ObligationNotReady, ObligationResult,
        infer::clause::ClauseObligation,
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
        self.oblige_ty_outlives_re(ClauseOrigin::never_printed(), other, joiner, dir.invert());

        // `universal: 'a` (inverse: `'a: universal`)
        self.permit_universe_re_outlives_re(universal, joiner, dir);
    }

    pub fn oblige_general_outlives(
        &mut self,
        origin: ClauseOrigin,
        lhs: TyOrRe,
        rhs: TyOrRe,
        dir: RelationDirection,
    ) {
        let (lhs, rhs) = dir.adapt(lhs, rhs);

        match (lhs, rhs) {
            (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                self.oblige_re_outlives_re(origin, lhs, rhs, RelationMode::LhsOntoRhs);
            }
            (TyOrRe::Ty(lhs), TyOrRe::Re(rhs)) => {
                self.oblige_ty_outlives_re(origin, lhs, rhs, RelationDirection::LhsOntoRhs);
            }
            (TyOrRe::Re(lhs), TyOrRe::Ty(rhs)) => {
                self.oblige_ty_outlives_re(origin, rhs, lhs, RelationDirection::RhsOntoLhs);
            }
            (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                self.oblige_ty_outlives_ty(origin, lhs, rhs);
            }
        }
    }

    pub fn oblige_ty_outlives_ty(&mut self, origin: ClauseOrigin, lhs: Ty, rhs: Ty) {
        // LHS: 'a
        // 'a: RHS
        // => LHS: RHS

        let joiner = self.fresh_re_infer();

        // LHS: 'a
        self.oblige_ty_outlives_re(origin.clone(), lhs, joiner, RelationDirection::LhsOntoRhs);

        // 'a: RHS
        self.oblige_ty_outlives_re(origin, rhs, joiner, RelationDirection::RhsOntoLhs);
    }

    pub fn oblige_ty_outlives_re(
        &mut self,
        origin: ClauseOrigin,
        lhs: Ty,
        rhs: Re,
        dir: RelationDirection,
    ) {
        self.push_obligation(ClauseObligation::TyOutlivesRe(origin, lhs, rhs, dir));
    }

    pub(super) fn run_oblige_ty_outlives_re(
        &mut self,
        origin: &ClauseOrigin,
        lhs: Ty,
        rhs: Re,
        dir: RelationDirection,
    ) -> ObligationResult {
        let s = self.session();

        match *lhs.r(s) {
            TyKind::SigThis
            | TyKind::SigInfer
            | TyKind::SigGeneric(_)
            | TyKind::SigProject(_)
            | TyKind::SigAlias(_, _)
            | TyKind::HrtbVar(_) => {
                unreachable!()
            }
            TyKind::Simple(_) | TyKind::Error(_) | TyKind::FnDef(_) => {
                // (trivial)
            }
            TyKind::Reference(lhs, _muta, _pointee) => {
                self.ucx_mut()
                    .unify_re_and_re(origin, lhs, rhs, dir.to_mode());
            }
            TyKind::Adt(lhs) => {
                // ADTs are bounded by which regions they mention.
                for &lhs in lhs.params.r(s) {
                    match lhs {
                        TyOrRe::Re(lhs) => {
                            self.ucx_mut()
                                .unify_re_and_re(origin, lhs, rhs, dir.to_mode());
                        }
                        TyOrRe::Ty(lhs) => {
                            self.oblige_ty_outlives_re(origin.clone(), lhs, rhs, dir);
                        }
                    }
                }
            }

            TyKind::Trait(lhs_re, _muta, _lhs_spec) => {
                self.ucx_mut()
                    .unify_re_and_re(origin, lhs_re, rhs, dir.to_mode());
            }
            TyKind::Tuple(lhs) => {
                for &lhs in lhs.r(s) {
                    self.oblige_ty_outlives_re(origin.clone(), lhs, rhs, dir);
                }
            }
            TyKind::UniversalVar(var) => {
                let lub_re = self.elaborate_ty_universal_clauses(var).lub_re;

                self.oblige_re_outlives_re(origin.clone(), lub_re, rhs, dir.to_mode());
            }
            TyKind::InferVar(inf_lhs) => {
                match self.ucx().lookup_ty_infer_var(inf_lhs) {
                    Ok(inf_lhs) => {
                        self.oblige_ty_outlives_re(origin.clone(), inf_lhs, rhs, dir);
                    }
                    Err(err) => {
                        if err.perm_set.contains(SimpleTySet::OTHER) {
                            return Err(ObligationNotReady);
                        }

                        // (trivially true of all remaining types)
                    }
                }
            }
        }

        Ok(())
    }
}
