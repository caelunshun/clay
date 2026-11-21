//! Logic to implement the outlives obligation.

use crate::{
    base::ListInternable,
    semantic::{
        infer::{
            ClauseCx, ClauseObligation, GeneralOutlivesError, GeneralOutlivesErrorKind,
            ObligationNotReady, ObligationResult, ObligationTermination, Promise, PromiseHandle,
            ReConstraintOrder,
        },
        syntax::{InferTyVar, Re, RelationMode, SimpleTySet, Ty, TyKind, TyOrRe, TyOrReList},
    },
};

impl<'sess> ClauseCx<'sess> {
    pub fn permit_outlives(
        &mut self,
        mode: RelationMode,
        lhs: impl Into<TyOrRe>,
        rhs: impl Into<TyOrRe>,
    ) {
        let s = self.session();

        let lhs = lhs.into();
        let rhs = rhs.into();

        if let (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) = (lhs, rhs) {
            self.permit_re_and_re(mode, [lhs], [rhs]);
            return;
        }

        self.permit_general_outlives(mode, lhs.intern_single(s), rhs.intern_single(s));
    }

    pub fn oblige_outlives(
        &mut self,
        mode: RelationMode,
        lhs: impl Into<TyOrRe>,
        rhs: impl Into<TyOrRe>,
    ) -> Promise<'sess, GeneralOutlivesError> {
        let s = self.session();

        let lhs = lhs.into();
        let rhs = rhs.into();

        if let (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) = (lhs, rhs) {
            return self
                .unify_re_and_re(mode, [lhs], [rhs])
                .map(move |ccx, error| {
                    let s = ccx.session();

                    GeneralOutlivesError {
                        lhs: TyOrRe::Re(lhs).intern_single(s),
                        rhs: TyOrRe::Re(lhs).intern_single(s),
                        mode,
                        error: GeneralOutlivesErrorKind::Unify(error),
                    }
                });
        }

        self.oblige_general_outlives(mode, lhs.intern_single(s), rhs.intern_single(s))
    }

    pub fn permit_general_outlives(
        &mut self,
        mode: RelationMode,
        lhs: TyOrReList,
        rhs: TyOrReList,
    ) {
        let order = self.next_re_constraint();

        self.push_obligation(ClauseObligation::Outlives {
            handle: None,
            mode,
            order,
            lhs,
            rhs,
        });
    }

    pub fn oblige_general_outlives(
        &mut self,
        mode: RelationMode,
        lhs: TyOrReList,
        rhs: TyOrReList,
    ) -> Promise<'sess, GeneralOutlivesError> {
        let (promise, handle) = Promise::new();
        let order = self.next_re_constraint();

        self.push_obligation(ClauseObligation::Outlives {
            handle: Some(handle),
            order,
            mode,
            lhs,
            rhs,
        });

        promise
    }

    pub(super) fn run_oblige_ty_outlives_re(
        &mut self,
        handle: Option<PromiseHandle<'sess, GeneralOutlivesError>>,
        order: ReConstraintOrder,
        mode: RelationMode,
        lhs: TyOrReList,
        rhs: TyOrReList,
    ) -> ObligationResult {
        let lhs_regions = self
            .collect_dominating_regions_in_ty_or_re_list(lhs)
            .map_err(ObligationNotReady::UnresolvedInfer)?;

        let rhs_regions = self
            .collect_dominating_regions_in_ty_or_re_list(rhs)
            .map_err(ObligationNotReady::UnresolvedInfer)?;

        if let Some(handle) = handle {
            self.ucx_mut()
                .unify_re_and_re(order, mode, lhs_regions, rhs_regions)
                .map(move |_ccx, error| GeneralOutlivesError {
                    lhs,
                    rhs,
                    mode,
                    error: GeneralOutlivesErrorKind::Unify(error),
                })
                .forward(self, handle);
        } else {
            self.permit_re_and_re(mode, lhs_regions, rhs_regions);
        }

        Ok(ObligationTermination::Finished)
    }

    fn collect_dominating_regions_in_ty_or_re_list(
        &mut self,
        list: TyOrReList,
    ) -> Result<Vec<Re>, InferTyVar> {
        let s = self.session();

        let mut collector = Vec::new();

        for &term in list.r(s) {
            match term {
                TyOrRe::Re(re) => {
                    collector.push(re);
                }
                TyOrRe::Ty(ty) => {
                    self.collect_dominating_regions_in_ty(&mut collector, ty)?;
                }
            }
        }

        Ok(collector)
    }

    fn collect_dominating_regions_in_ty(
        &mut self,
        collector: &mut Vec<Re>,
        ty: Ty,
    ) -> Result<(), InferTyVar> {
        let s = self.session();

        match *ty.r(s) {
            TyKind::HrtbVar(_) | TyKind::HrtbProjection(_) => {
                unreachable!()
            }
            TyKind::Simple(_) | TyKind::Error(_) | TyKind::FnDef(_) => {
                // (trivial)
            }
            TyKind::Reference(re, _muta, _pointee) => {
                collector.push(re);
            }
            TyKind::Adt(ty) => {
                // ADTs are bounded by the regions which they mention.
                for &para in ty.params.r(s) {
                    match para {
                        TyOrRe::Re(re) => {
                            collector.push(re);
                        }
                        TyOrRe::Ty(ty) => {
                            self.collect_dominating_regions_in_ty(collector, ty)?;
                        }
                    }
                }
            }

            TyKind::Trait(re, _muta, _spec) => {
                collector.push(re);
            }
            TyKind::Tuple(elems) => {
                for &ty in elems.r(s) {
                    self.collect_dominating_regions_in_ty(collector, ty)?;
                }
            }
            TyKind::Universal(universal) => {
                let re_representative = self
                    .elaborate_universal_immediately(universal)
                    .re_representative;

                collector.push(re_representative);
            }
            TyKind::InferVar(var) => {
                match self.ucx().lookup_ty_infer_var(var) {
                    Ok(resolved) => {
                        self.collect_dominating_regions_in_ty(collector, resolved)?;
                    }
                    Err(err) => {
                        if err.perm_set.intersects(SimpleTySet::OTHER) {
                            return Err(var);
                        }

                        // (all remaining types are trivial)
                    }
                }
            }
        }

        Ok(())
    }
}
