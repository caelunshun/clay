//! Logic to implement the type-implements-trait obligation.

use crate::{
    base::arena::{HasInterner as _, Obj},
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnv, ClauseOrigin, NoTraitImplError, ObligationNotReady,
            ObligationResult, TyFolderInfallibleExt, UnboundVarHandlingMode, UniversalElaboration,
            infer::clause::ClauseObligation,
        },
        syntax::{
            HrtbBinder, ImplItem, RelationMode, TraitClause, TraitClauseList, TraitParam,
            TraitSpec, Ty, TyKind, TyOrRe,
        },
    },
};

#[derive(Debug, Clone)]
struct SelectionRejected;

impl<'tcx> ClauseCx<'tcx> {
    pub fn oblige_ty_meets_clauses(
        &mut self,
        origin: &ClauseOrigin,
        lhs: Ty,
        rhs: TraitClauseList,
    ) {
        let s = self.session();

        for &clause in rhs.r(s) {
            self.oblige_ty_meets_clause(origin.clone(), lhs, clause);
        }
    }

    pub fn oblige_ty_meets_clause(&mut self, origin: ClauseOrigin, lhs: Ty, rhs: TraitClause) {
        match rhs {
            TraitClause::Outlives(rhs_dir, rhs) => {
                self.oblige_general_outlives(origin, TyOrRe::Ty(lhs), rhs, rhs_dir);
            }
            TraitClause::Trait(rhs) => {
                self.oblige_ty_meets_trait(origin, lhs, rhs);
            }
        }
    }

    pub fn oblige_ty_meets_trait(
        &mut self,
        origin: ClauseOrigin,
        lhs: Ty,
        rhs: HrtbBinder<TraitSpec>,
    ) {
        let rhs = self.instantiate_hrtb_universal(rhs);
        self.oblige_ty_meets_trait_instantiated(origin, lhs, rhs)
    }

    pub fn oblige_ty_meets_trait_instantiated(
        &mut self,
        origin: ClauseOrigin,
        lhs: Ty,
        rhs: TraitSpec,
    ) {
        self.push_obligation(ClauseObligation::TyMeetsTrait(origin, lhs, rhs));
    }

    pub(super) fn run_oblige_ty_meets_trait_instantiated(
        &mut self,
        origin: &ClauseOrigin,
        lhs: Ty,
        rhs: TraitSpec,
    ) -> ObligationResult<Result<(), NoTraitImplError>> {
        let tcx = self.tcx();
        let s = self.session();

        // See whether the type itself can provide the implementation.
        match *self.ucx().peel_ty_infer_var(lhs).r(s) {
            TyKind::Trait(_re, _muta, clauses) => {
                todo!()
            }
            TyKind::UniversalVar(universal) => {
                match self
                    .clone()
                    .try_select_inherent_impl(origin, self.elaborate_ty_universal_clauses(universal), rhs)
                {
                    Ok(res) => {
                        *self = res;
                        return Ok(Ok(()));
                    }
                    Err(SelectionRejected) => {
                        // (fallthrough)
                    }
                }
            }
            TyKind::InferVar(_) => {
                // We can't yet rule out the possibility that this obligation is inherently
                // fulfilled.
                return Err(ObligationNotReady);
            }
            TyKind::Error(_) => {
                // Error types can do anything.
                return Ok(Ok(()));
            }
            TyKind::SigThis
            | TyKind::SigInfer
            | TyKind::SigGeneric(_)
            | TyKind::SigProject(_)
            // LHS HRTBs should have been instantiated right before the obligation.
            | TyKind::HrtbVar(_) => {
                unreachable!()
            }
            TyKind::Simple(_)
            | TyKind::Reference(_, _, _)
            | TyKind::Adt(_)
            | TyKind::Tuple(_)
            | TyKind::FnDef(_) => {
                // (the `impl` must come externally, fallthrough)
            }
        }

        // Otherwise, scan for a suitable `impl`.
        let mut prev_confirmation = None;

        let candidates = self.coherence().gather_impl_candidates(
            tcx,
            self.ucx()
                .substitutor(UnboundVarHandlingMode::EraseToSigInfer)
                .fold(lhs),
            self.ucx()
                .substitutor(UnboundVarHandlingMode::EraseToSigInfer)
                .fold(rhs),
        );

        if let Ok(confirmation) = self.clone().try_select_special_impl(origin, lhs, rhs) {
            debug_assert!(prev_confirmation.is_none());
            prev_confirmation = Some(confirmation)
        }

        for candidate in candidates {
            let Ok(confirmation) = self
                .clone()
                .try_select_block_impl(origin, lhs, candidate, rhs)
            else {
                continue;
            };

            if prev_confirmation.is_some() {
                return Err(ObligationNotReady);
            }

            prev_confirmation = Some(confirmation)
        }

        let Some(confirmation) = prev_confirmation else {
            return Ok(Err(NoTraitImplError {
                origin: origin.clone(),
                target: lhs,
                spec: rhs,
            }));
        };

        *self = confirmation;

        Ok(Ok(()))
    }

    fn try_select_inherent_impl(
        mut self,
        origin: &ClauseOrigin,
        lhs: UniversalElaboration,
        rhs: TraitSpec,
    ) -> Result<Self, SelectionRejected> {
        let s = self.session();

        // Find the clause that could prove our trait.
        let lhs = lhs
            .clauses
            .r(s)
            .iter()
            .copied()
            .find(|&clause| match clause {
                TraitClause::Outlives(_, _) => false,
                TraitClause::Trait(lhs) => lhs.inner.def == rhs.def,
            });

        let Some(lhs) = lhs else {
            return Err(SelectionRejected);
        };

        let TraitClause::Trait(lhs) = lhs else {
            unreachable!()
        };

        // Instantiate the binder with inference variables so that we may select the correct
        // implementation of it.
        let lhs = self.instantiate_hrtb_infer(origin, lhs);

        // See whether we can select an inherent `impl`.
        let mut param_iter = lhs.params.r(s).iter().zip(rhs.params.r(s));

        for (&lhs_param, &rhs_param) in
            (&mut param_iter).take(*rhs.def.r(s).regular_generic_count as usize)
        {
            let TraitParam::Equals(lhs) = lhs_param else {
                unreachable!();
            };

            match rhs_param {
                TraitParam::Equals(rhs) => match (lhs, rhs) {
                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                        // This can be an obligation because selection shouldn't depend on regions.
                        self.oblige_re_outlives_re(origin.clone(), lhs, rhs, RelationMode::Equate);
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        if let Err(_err) =
                            self.ucx_mut()
                                .unify_ty_and_ty(origin, lhs, rhs, RelationMode::Equate)
                        {
                            return Err(SelectionRejected);
                        }
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(_) => {
                    unreachable!()
                }
            }
        }

        // If we can, push its obligations.
        for (&lhs_param, &rhs_param) in param_iter {
            let TraitParam::Equals(lhs) = lhs_param else {
                unreachable!();
            };

            match rhs_param {
                TraitParam::Equals(rhs) => match (lhs, rhs) {
                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                        self.oblige_re_outlives_re(origin.clone(), lhs, rhs, RelationMode::Equate);
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        self.oblige_ty_unifies_ty(origin.clone(), lhs, rhs, RelationMode::Equate);
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(rhs) => match lhs {
                    TyOrRe::Re(lhs) => {
                        self.oblige_re_meets_clauses(origin, lhs, rhs);
                    }
                    TyOrRe::Ty(lhs) => {
                        self.oblige_ty_meets_clauses(origin, lhs, rhs);
                    }
                },
            }
        }

        Ok(self)
    }

    fn try_select_block_impl(
        mut self,
        origin: &ClauseOrigin,
        lhs: Ty,
        rhs: Obj<ImplItem>,
        spec: TraitSpec,
    ) -> Result<Self, SelectionRejected> {
        let s = self.session();

        // Obtain inference variables for all generics in the `impl` and tentatively create
        // obligations for them.
        let trait_env = self.instantiate_binder_list_as_infer(
            origin,
            ClauseImportEnv::new(lhs, Vec::new()),
            &[rhs.r(s).generics],
        );

        // Import the target type and trait. WF obligations are not needed on these types because
        // the `impl` itself has been WF-checked for all types compatible with the generic
        // parameters.
        let target_ty = self
            .importer(trait_env.as_ref())
            .fold_spanned(rhs.r(s).target);

        let target_trait = self
            .importer(trait_env.as_ref())
            .fold_spanned(rhs.r(s).trait_.unwrap());

        // Does the `lhs` type match the `rhs`'s target type?
        if self
            .ucx_mut()
            .unify_ty_and_ty(origin, lhs, target_ty, RelationMode::Equate)
            .is_err()
        {
            return Err(SelectionRejected);
        }

        // See whether our RHS trait's generic parameters can be satisfied by this `impl`.
        debug_assert_eq!(target_trait.def, spec.def);

        for (&instance, &required_param) in target_trait
            .params
            .r(s)
            .iter()
            .zip(spec.params.r(s))
            .take(*spec.def.r(s).regular_generic_count as usize)
        {
            match required_param {
                TraitParam::Equals(required) => match (instance, required) {
                    (TyOrRe::Re(instance), TyOrRe::Re(required)) => {
                        self.ucx_mut().unify_re_and_re(
                            origin,
                            instance,
                            required,
                            RelationMode::Equate,
                        );
                    }
                    (TyOrRe::Ty(instance), TyOrRe::Ty(required)) => {
                        if self
                            .ucx_mut()
                            .unify_ty_and_ty(origin, instance, required, RelationMode::Equate)
                            .is_err()
                        {
                            return Err(SelectionRejected);
                        }
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(_) => {
                    unreachable!()
                }
            }
        }

        // Register obligations for associated types.
        for (&instance_ty, &required_param) in target_trait
            .params
            .r(s)
            .iter()
            .zip(spec.params.r(s))
            .skip(*spec.def.r(s).regular_generic_count as usize)
        {
            // Associated types are never regions.
            let instance_ty = instance_ty.unwrap_ty();

            match required_param {
                TraitParam::Equals(required_ty) => {
                    let TyOrRe::Ty(required_ty) = required_ty else {
                        unreachable!()
                    };

                    self.oblige_ty_unifies_ty(
                        origin.clone(),
                        instance_ty,
                        required_ty,
                        RelationMode::Equate,
                    );
                }
                TraitParam::Unspecified(additional_clauses) => {
                    self.oblige_ty_meets_clauses(origin, instance_ty, additional_clauses);
                }
            }
        }

        Ok(self)
    }

    fn try_select_special_impl(
        mut self,
        origin: &ClauseOrigin,
        lhs: Ty,
        rhs: TraitSpec,
    ) -> Result<Self, SelectionRejected> {
        let s = self.session();
        let tcx = self.tcx();
        let krate = self.krate();
        let lhs = self.ucx().peel_ty_infer_var(lhs);

        if (Some(rhs.def) == krate.r(s).fn_once_lang_item(s)
            || Some(rhs.def) == krate.r(s).fn_mut_lang_item(s)
            || Some(rhs.def) == krate.r(s).fn_lang_item(s))
            && let TyKind::FnDef(lhs) = *lhs.r(s)
        {
            let &[
                TraitParam::Equals(TyOrRe::Ty(rhs_input)),
                TraitParam::Equals(TyOrRe::Ty(rhs_output)),
            ] = rhs.params.r(s)
            else {
                unreachable!()
            };

            let (lhs_input, lhs_output) = self.instantiate_fn_instance_sig(origin, lhs);
            let lhs_input = tcx.intern(TyKind::Tuple(lhs_input));

            if self
                .ucx_mut()
                .unify_ty_and_ty(origin, lhs_input, rhs_input, RelationMode::Equate)
                .is_err()
            {
                return Err(SelectionRejected);
            }

            if self
                .ucx_mut()
                .unify_ty_and_ty(origin, lhs_output, rhs_output, RelationMode::Equate)
                .is_err()
            {
                return Err(SelectionRejected);
            }

            return Ok(self);
        }

        Err(SelectionRejected)
    }
}
