//! Logic to implement the outlives obligation.

use crate::semantic::{
    infer::{
        ClauseCx, ClauseObligation, GeneralOutlivesError, MultiPromiseBuilder, ObligationNotReady,
        ObligationResult, ObligationTermination, Promise, PromiseHandle, ReConstraintOrder,
        TyOutlivesReError, TyOutlivesReErrorCulprit, TyOutlivesTyError,
    },
    syntax::{
        InferTyVar, Re, RelationDirection, RelationMode, SimpleTySet, Ty, TyKind, TyOrRe,
        UniversalReVarSourceInfo,
    },
};

impl<'sess> ClauseCx<'sess> {
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
        // permit(universal: 'a)
        // constrain('a: other)
        // =>
        // permit(universal: other)
        // ```
        //
        // If `dir == RhsOntoLhs`...
        //
        // ```
        // permit('a: universal)
        // constrain(other: 'a)
        // =>
        // permit(other: universal)
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
    ) -> Promise<'sess, GeneralOutlivesError> {
        let (lhs, rhs) = dir.adapt(lhs, rhs);

        match (lhs, rhs) {
            (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => self
                .unify_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs)
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

    pub fn obtain_ty_lub(&mut self, ty: Ty) -> Re {
        // The universal will range over all lifetimes which outlive the `ty`, including the genuine
        // LUB, which is the most restrictive case. In other words, creating this as a universal
        // forces the lifetime to act like the LUB.

        let universal = self.fresh_re_universal(UniversalReVarSourceInfo::OutliveLub(ty));
        self.permit_universe_re_outlives_ty(universal, ty, RelationDirection::LhsOntoRhs);

        universal
    }

    pub fn obtain_ty_glb(&mut self, ty: Ty) -> Re {
        // See `obtain_ty_lub`.

        let universal = self.fresh_re_universal(UniversalReVarSourceInfo::OutliveGlb(ty));
        self.permit_universe_re_outlives_ty(universal, ty, RelationDirection::RhsOntoLhs);

        universal
    }

    pub fn oblige_ty_outlives_ty(&mut self, lhs: Ty, rhs: Ty) -> Promise<'sess, TyOutlivesTyError> {
        // One would think they could just run...
        //
        // ```
        // 'joiner = fresh_infer()
        // constrain(lhs: &longer 'joiner)
        // constrain('joiner: rhs)
        // ```
        //
        // This, however, would reject `(&'a (), &'b ()): &longer (&'a (), &'b ())` where `'a, 'b`
        // are universals. To understand why, check out this neat hasse diagram!
        //
        // ```
        //               ┌──────┐
        //        ┌─────►│ 'gc  │◄────┐
        //        │      └──────┘     │
        //        │                   │
        //        │ ┌──►'?joiner◄───┐ │
        //        │ ┼               ┼ │
        //      ┌─┴─┴─┐            ┌┴─┴──┐
        // ░░░░░│ 'a  │░░░░░░░░░░░░│ 'b  │░░░░░
        //      └─▲─▲─┘            └▲─▲──┘
        //        │ ┼               ┼ │
        //        │ └───'?joiner────┘ │
        //        │                   │
        //        │                   │
        //        │    ┌──────────┐   │
        //        └────┤ 'bottom  ├───┘
        //             └──────────┘
        // ```
        //
        // Legend:
        //
        // - Boxed lifetimes are universals
        // - Lifetimes without boxes with a question mark in front are inference lifetimes.
        // - The lines without the dashes indicate universal permissions
        // - The lines with the dashes indicate constraints
        // - Note that `'bottom` is a virtual lifetime that cannot actually be mentioned by users.
        //   This ensures that we can do mention analysis to figure out a lower bound for associated
        //   types that don't give any additional bounds since we know projections can only mention
        //   their inputs.
        //
        // The `joiner` inference lifetime simultaneously has to be somewhere above `'a` and `'b`
        // *and*, simultaneously, below it as well!
        //
        // So, what's the actual solution?
        //
        // For `LHS: &longer RHS`, it has to be that, if *all parts of* the RHS are live, *all parts
        // of* the LHS must also be live.
        //
        // If we compute the greatest lower bound of the RHS using `obtain_ty_glb`, we'll create a
        // universal which can range over anything so long as the RHS outlives it, including a
        // maximally strict bound which is longer than all lifetimes except the lifetimes living
        // longer than *at least one* of the lifetimes mentioned in the RHS.
        //
        // In other words, if the LHS outlives the RHS's GLB, we'll know that if all lifetimes in
        // the RHS are live, all lifetimes in the LHS will also be live since they must outlive at
        // least one of those RHS lifetimes.
        //
        // See the `ty_outlives.clay` uitest for an exercising of this logic.

        let rhs_glb = self.obtain_ty_glb(rhs);

        // LHS: 'a
        self.oblige_ty_outlives_re(lhs, rhs_glb, RelationDirection::LhsOntoRhs)
            .map(move |_ccx, error| TyOutlivesTyError {
                lhs,
                rhs,
                rhs_glb,
                errors: error.errors,
            })
    }

    pub fn oblige_ty_outlives_re(
        &mut self,
        lhs: Ty,
        rhs: Re,
        dir: RelationDirection,
    ) -> Promise<'sess, TyOutlivesReError> {
        let (promise, handle) = Promise::new();
        let order = self.next_re_constraint();

        self.push_obligation(ClauseObligation::TyOutlivesRe {
            handle,
            order,
            lhs,
            rhs,
            dir,
        });

        promise
    }

    pub(super) fn run_oblige_ty_outlives_re(
        &mut self,
        handle: PromiseHandle<'sess, TyOutlivesReError>,
        order: ReConstraintOrder,
        lhs: Ty,
        rhs: Re,
        dir: RelationDirection,
    ) -> ObligationResult {
        let mut collector = MultiPromiseBuilder::new();

        if let Err(inf_var) =
            self.run_oblige_ty_outlives_re_inner(&mut collector, order, lhs, rhs, dir)
        {
            return Err(ObligationNotReady::UnresolvedInfer(inf_var));
        }

        collector
            .finish()
            .map(move |_ccx, errors| TyOutlivesReError { lhs, rhs, errors })
            .forward(self, handle);

        Ok(ObligationTermination::Finished)
    }

    fn run_oblige_ty_outlives_re_inner(
        &mut self,
        collector: &mut MultiPromiseBuilder<'sess, TyOutlivesReErrorCulprit>,
        order: ReConstraintOrder,
        lhs: Ty,
        rhs: Re,
        dir: RelationDirection,
    ) -> Result<(), InferTyVar> {
        let s = self.session();

        match *lhs.r(s) {
            TyKind::HrtbVar(_) | TyKind::HrtbProjection(_) => {
                unreachable!()
            }
            TyKind::Simple(_) | TyKind::Error(_) | TyKind::FnDef(_) => {
                // (trivial)
            }
            TyKind::Reference(lhs, _muta, _pointee) => {
                self.ucx_mut()
                    .unify_re_and_re(order, lhs, rhs, dir.to_mode())
                    .map(|_ccx, error| TyOutlivesReErrorCulprit::Regular(error))
                    .join(collector);
            }
            TyKind::Adt(lhs) => {
                // ADTs are bounded by the regions which they mention.
                for &lhs in lhs.params.r(s) {
                    match lhs {
                        TyOrRe::Re(lhs) => {
                            self.ucx_mut()
                                .unify_re_and_re(order, lhs, rhs, dir.to_mode())
                                .map(|_ccx, error| TyOutlivesReErrorCulprit::Regular(error))
                                .join(collector);
                        }
                        TyOrRe::Ty(lhs) => {
                            self.run_oblige_ty_outlives_re_inner(collector, order, lhs, rhs, dir)?;
                        }
                    }
                }
            }

            TyKind::Trait(lhs_re, _muta, _lhs_spec) => {
                self.ucx_mut()
                    .unify_re_and_re(order, lhs_re, rhs, dir.to_mode())
                    .map(|_ccx, error| TyOutlivesReErrorCulprit::Regular(error))
                    .join(collector);
            }
            TyKind::Tuple(lhs) => {
                for &lhs in lhs.r(s) {
                    self.run_oblige_ty_outlives_re_inner(collector, order, lhs, rhs, dir)?;
                }
            }
            TyKind::Universal(universal) => {
                let lub_re = self.elaborate_universal_immediately(universal).lub_re;

                self.ucx_mut()
                    .unify_re_and_re(order, lub_re, rhs, dir.to_mode())
                    .map(|_ccx, error| TyOutlivesReErrorCulprit::Regular(error))
                    .join(collector);
            }
            TyKind::InferVar(inf_lhs) => {
                match self.ucx().lookup_ty_infer_var(inf_lhs) {
                    Ok(inf_lhs) => {
                        self.run_oblige_ty_outlives_re_inner(collector, order, inf_lhs, rhs, dir)?;
                    }
                    Err(err) => {
                        if err.perm_set.intersects(SimpleTySet::OTHER) {
                            return Err(inf_lhs);
                        }

                        // (trivially true of all remaining types)
                    }
                }
            }
        }

        Ok(())
    }
}
