//! Logic to implement the type-implements-trait obligation.

use super::elaboration::{UniversalElaboration, WipReificationRootSet};
use crate::{
    base::arena::{HasInterner as _, Obj},
    semantic::{
        infer::{
            ClauseCx, ClauseObligation, HrtbUniverse, HrtbUniverseInfo, InstantiatedImplBlock,
            NoTraitImplError, NotCoveredError, ObligationNotReady, ObligationResult, ObligeCause,
            ObligeCauseStep,
        },
        syntax::{
            HrtbBinder, ImplItem, RelationMode, SimpleTySet, TraitClause, TraitClauseList,
            TraitParam, TraitSpec, Ty, TyCtxt, TyKind, TyOrRe, TyVisitor, TyVisitorInfallibleExt,
            UniversalTyVar,
        },
    },
    utils::hash::FxHashMap,
};
use std::{convert::Infallible, ops::ControlFlow, rc::Rc};

#[derive(Debug, Clone)]
struct SelectionRejected;

// TODO: Give more information to causes
impl<'tcx> ClauseCx<'tcx> {
    pub fn oblige_ty_meets_clauses(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        lhs: Ty,
        rhs: TraitClauseList,
    ) {
        let s = self.session();

        for &clause in rhs.r(s) {
            self.oblige_ty_meets_clause(cause.clone(), universe, lhs, clause);
        }
    }

    pub fn oblige_ty_meets_clause(
        &mut self,
        cause: ObligeCause,
        universe: &HrtbUniverse,
        lhs: Ty,
        rhs: TraitClause,
    ) {
        match rhs {
            TraitClause::Outlives(rhs_dir, rhs) => {
                self.oblige_general_outlives(cause, TyOrRe::Ty(lhs), rhs, rhs_dir);
            }
            TraitClause::Trait(rhs) => {
                self.oblige_ty_meets_trait(cause, universe.clone(), lhs, rhs);
            }
        }
    }

    pub fn oblige_ty_meets_trait(
        &mut self,
        cause: ObligeCause,
        universe: HrtbUniverse,
        lhs: Ty,
        rhs: HrtbBinder,
    ) {
        let s = self.session();

        let universe = {
            if rhs.defs.r(s).is_empty() {
                universe
            } else {
                universe.nest(HrtbUniverseInfo {
                    cause: cause.clone(),
                })
            }
        };

        let rhs = self.instantiate_hrtb_universal(&cause, universe.clone(), rhs);
        self.oblige_ty_meets_trait_instantiated(cause, universe, lhs, rhs)
    }

    pub fn oblige_ty_meets_trait_instantiated(
        &mut self,
        cause: ObligeCause,
        universe: HrtbUniverse,
        lhs: Ty,
        rhs: TraitSpec,
    ) {
        self.push_obligation(ClauseObligation::TyMeetsTrait(
            cause.child(ObligeCauseStep::ImplInstantiatedClause { lhs, rhs }.into()),
            universe,
            lhs,
            rhs,
        ));
    }

    pub(super) fn run_oblige_ty_meets_trait_instantiated(
        &mut self,
        cause: &ObligeCause,
        universe: HrtbUniverse,
        lhs: Ty,
        rhs: TraitSpec,
    ) -> ObligationResult<Result<(), NoTraitImplError>> {
        let s = self.session();

        // See whether the type itself can provide the implementation.
        match *self.ucx().peel_ty_infer_var(lhs).r(s) {
            TyKind::Trait(_re, _muta, clauses) => {
                todo!()
            }
            TyKind::UniversalVar(universal) => {
                let universal_elab =
                    self.elaborate_ty_universal_clauses_possibly_floating(universal);

                match self.clone().try_select_inherent_impl(
                    cause,
                    &universe,
                    universal_elab,
                    rhs,
                )? {
                    Ok(res) => {
                        *self = res;
                        return Ok(Ok(()));
                    }
                    Err(SelectionRejected) => {
                        // (fallthrough)
                    }
                }
            }
            TyKind::InferVar(var) => {
                let is_possibly_universal = self
                    .lookup_ty_infer_var_without_poll(var)
                    .unwrap_err()
                    .perm_set
                    .intersects(SimpleTySet::MAYBE_UNIVERSAL);

                if is_possibly_universal {
                    // We can't yet rule out the possibility that this obligation is inherently
                    // fulfilled.
                    return Err(ObligationNotReady::UnresolvedInfer(var));
                }
            }
            TyKind::Error(_) => {
                // Error types can do anything.
                return Ok(Ok(()));
            }

            // LHS HRTBs should have been instantiated right before the obligation.
            TyKind::HrtbVar(_) | TyKind::HrtbProjection(_) => {
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

        let candidates = self
            .coherence()
            .gather_trait_impl_candidates(self, lhs, rhs);

        if let Ok(confirmation) = self
            .clone()
            .try_select_special_impl(cause, &universe, lhs, rhs)
        {
            debug_assert!(prev_confirmation.is_none());
            prev_confirmation = Some(confirmation)
        }

        for candidate in candidates {
            let Ok(confirmation) = self
                .clone()
                .try_select_block_impl(cause, &universe, lhs, candidate, rhs)
            else {
                continue;
            };

            if prev_confirmation.is_some() {
                return Err(ObligationNotReady::MultipleApplicableImpls);
            }

            prev_confirmation = Some(confirmation)
        }

        let Some(confirmation) = prev_confirmation else {
            return Ok(Err(NoTraitImplError {
                cause: cause.clone(),
                target: lhs,
                spec: rhs,
            }));
        };

        *self = confirmation;

        Ok(Ok(()))
    }

    fn try_select_inherent_impl(
        self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        lhs: UniversalElaboration,
        rhs: TraitSpec,
    ) -> ObligationResult<Result<Self, SelectionRejected>> {
        let s = self.session();

        let reified_var_roots = lhs.collect_roots_if_floating(&self);

        for &lhs in lhs.clauses.r(s) {
            let TraitClause::Trait(lhs) = lhs else {
                continue;
            };

            if lhs.inner.def != rhs.def {
                continue;
            }

            if let Ok(fork) = self.clone().try_select_single_inherent_impl(
                cause,
                universe,
                lhs,
                rhs,
                reified_var_roots.as_ref(),
            )? {
                return Ok(Ok(fork));
            }
        }

        Ok(Err(SelectionRejected))
    }

    fn try_select_single_inherent_impl(
        mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        lhs: HrtbBinder,
        rhs: TraitSpec,
        reified_var_roots: Option<&WipReificationRootSet>,
    ) -> ObligationResult<Result<Self, SelectionRejected>> {
        let s = self.session();

        assert_eq!(lhs.inner.def, rhs.def);

        let is_ready_if_selected =
            self.is_elaborated_clause_ready_if_selected(reified_var_roots, lhs);

        // See whether we can select this inherent `impl`.
        let cause = cause
            .clone()
            .child(ObligeCauseStep::ImplUsingInherent { lhs, rhs }.into());

        let lhs = self.instantiate_hrtb_infer(cause.clone(), universe.clone(), lhs);

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
                        self.oblige_re_outlives_re(cause.clone(), lhs, rhs, RelationMode::Equate);
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        // See whether we can reject this parameter.
                        if let Err(_err) = self.ucx_mut().unify_ty_and_ty(
                            &ObligeCause::new_never_report(),
                            lhs,
                            rhs,
                            RelationMode::Equate,
                        ) {
                            return Ok(Err(SelectionRejected));
                        }
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(_) => {
                    unreachable!()
                }
            }
        }

        // If we couldn't definitively reject this clause and it's unfinished, we need to wait for
        // more inferences. This is important because, otherwise, we could either select the
        // incorrect clause if the generic parameters contain unresolved projections or even
        // possibly allow a recursive projection to compile.
        if !is_ready_if_selected {
            return Err(ObligationNotReady::ElaborationHasInferForInherentSelection);
        }

        // If we can, push its obligations.
        for (&lhs_param, &rhs_param) in param_iter {
            let TraitParam::Equals(lhs) = lhs_param else {
                unreachable!();
            };

            match rhs_param {
                TraitParam::Equals(rhs) => match (lhs, rhs) {
                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                        self.oblige_re_outlives_re(cause.clone(), lhs, rhs, RelationMode::Equate);
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        self.oblige_ty_unifies_ty(cause.clone(), lhs, rhs, RelationMode::Equate);
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(rhs) => match lhs {
                    TyOrRe::Re(lhs) => {
                        self.oblige_re_meets_clauses(&cause, lhs, rhs);
                    }
                    TyOrRe::Ty(lhs) => {
                        self.oblige_ty_meets_clauses(&cause, universe, lhs, rhs);
                    }
                },
            }
        }

        Ok(Ok(self))
    }

    fn try_select_block_impl(
        mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        lhs: Ty,
        rhs: Obj<ImplItem>,
        spec: TraitSpec,
    ) -> Result<Self, SelectionRejected> {
        let s = self.session();

        // Obtain inference variables for all generics in the `impl` and tentatively create
        // obligations for them.
        let InstantiatedImplBlock {
            target_ty,
            target_trait,
            ..
        } = self
            .instantiate_infer()
            .fresh_impl_block(cause, universe, rhs);

        let target_trait = target_trait.unwrap();

        // Does the `lhs` type match the `rhs`'s target type?
        if self
            .ucx_mut()
            .unify_ty_and_ty(cause, lhs, target_ty, RelationMode::Equate)
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
                            cause,
                            instance,
                            required,
                            RelationMode::Equate,
                        );
                    }
                    (TyOrRe::Ty(instance), TyOrRe::Ty(required)) => {
                        if self
                            .ucx_mut()
                            .unify_ty_and_ty(cause, instance, required, RelationMode::Equate)
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
                        cause.clone(),
                        instance_ty,
                        required_ty,
                        RelationMode::Equate,
                    );
                }
                TraitParam::Unspecified(additional_clauses) => {
                    self.oblige_ty_meets_clauses(cause, universe, instance_ty, additional_clauses);
                }
            }
        }

        Ok(self)
    }

    fn try_select_special_impl(
        mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        lhs: Ty,
        rhs: TraitSpec,
    ) -> Result<Self, SelectionRejected> {
        let s = self.session();
        let tcx = self.tcx();
        let krate = self.krate();
        let lhs = self.ucx().peel_ty_infer_var(lhs);

        let lang_items = &krate.r(s).lang_items;

        if (Some(rhs.def) == lang_items.fn_once_trait()
            || Some(rhs.def) == lang_items.fn_mut_trait()
            || Some(rhs.def) == lang_items.fn_trait())
            && let TyKind::FnDef(instance) = *lhs.r(s)
        {
            let &[
                TraitParam::Equals(TyOrRe::Ty(rhs_input)),
                TraitParam::Equals(TyOrRe::Ty(rhs_output)),
            ] = rhs.params.r(s)
            else {
                unreachable!()
            };

            let sig = self
                .instantiate_infer()
                .resolve_fn_instance_sig(cause, universe, instance);

            if self
                .ucx_mut()
                .unify_ty_and_ty(
                    cause,
                    rhs_input,
                    tcx.intern(TyKind::Tuple(sig.args)),
                    RelationMode::Equate,
                )
                .is_err()
            {
                return Err(SelectionRejected);
            }

            if self
                .ucx_mut()
                .unify_ty_and_ty(cause, rhs_output, sig.ret_ty, RelationMode::Equate)
                .is_err()
            {
                return Err(SelectionRejected);
            }

            return Ok(self);
        }

        Err(SelectionRejected)
    }

    pub fn oblige_covered(
        &mut self,
        cause: ObligeCause,
        must_mention: impl IntoIterator<Item = UniversalTyVar>,
        in_type: Option<Ty>,
        in_trait: Option<TraitSpec>,
    ) {
        let mut counter = 0u32;
        let must_mention = Rc::new(
            must_mention
                .into_iter()
                .map(|k| {
                    let id = counter;
                    counter += 1;
                    (k, id)
                })
                .collect::<FxHashMap<_, _>>(),
        );

        self.push_obligation(ClauseObligation::Covered(
            cause,
            must_mention,
            in_type,
            in_trait,
        ));
    }

    pub(super) fn run_oblige_covered(
        &mut self,
        cause: ObligeCause,
        must_mention: Rc<FxHashMap<UniversalTyVar, u32>>,
        in_type: Option<Ty>,
        in_trait: Option<TraitSpec>,
    ) -> ObligationResult<()> {
        struct CoverVisitor<'a, 'tcx> {
            ccx: &'a ClauseCx<'tcx>,
            must_mention: Rc<FxHashMap<UniversalTyVar, u32>>,
            cover_set: Vec<bool>,
            had_holes: bool,
        }

        impl<'tcx> TyVisitor<'tcx> for CoverVisitor<'_, 'tcx> {
            type Break = Infallible;

            fn tcx(&self) -> &'tcx TyCtxt {
                self.ccx.tcx()
            }

            fn visit_ty(&mut self, ty: Ty) -> ControlFlow<Self::Break> {
                let s = self.session();

                match *ty.r(s) {
                    TyKind::InferVar(var) => {
                        if let Ok(peeled) = self.ccx.lookup_ty_infer_var_without_poll(var) {
                            self.visit(peeled);
                        } else {
                            self.had_holes = true;
                        }
                    }
                    TyKind::UniversalVar(var) => {
                        if let Some(&must_mention) = self.must_mention.get(&var) {
                            self.cover_set[must_mention as usize] = true;
                        }
                    }
                    _ => {
                        self.walk(ty);
                    }
                }

                ControlFlow::Continue(())
            }
        }

        let cover_set = must_mention.iter().map(|_| false).collect::<Vec<_>>();
        let mut visitor = CoverVisitor {
            ccx: self,
            must_mention,
            cover_set,
            had_holes: false,
        };

        if let Some(ty_part) = in_type {
            visitor.visit(ty_part);
        }

        if let Some(trait_part) = in_trait {
            visitor.visit(trait_part);
        }

        let missing_mentions = visitor
            .must_mention
            .iter()
            .filter(|(_var, idx)| !visitor.cover_set[**idx as usize])
            .map(|(var, _idx)| *var)
            .collect::<Vec<_>>();

        if missing_mentions.is_empty() {
            return Ok(());
        }

        if visitor.had_holes {
            return Err(ObligationNotReady::CoverMissingInfer);
        }

        NotCoveredError {
            cause,
            missing_mentions,
            in_trait,
            in_type,
        }
        .report(self);

        Ok(())
    }
}
