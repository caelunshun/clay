//! Logic to implement the type-implements-trait obligation.

use super::elaboration::{UniversalElaboration, WipReificationRootSet};
use crate::{
    base::arena::{HasInterner as _, Obj},
    semantic::{
        infer::{
            BlockImplUnsatisfiedError, ClauseCx, ClauseFuel, ClauseObligation, HrtbUniverse,
            HrtbUniverseInfo, InherentImplErrorImplCulprit, InherentImplUnsatisfiedError,
            InstantiatedImplBlock, InstantiatedTraitImplError, InstantiatedTraitImplErrorKind,
            MultiPromise, MultiPromiseBuilder, NotCoveredError, ObligationNotReady,
            ObligationResult, Promise, PromiseHandle, PromiseValue, TraitClauseError,
            UninstantiatedTraitImplError,
        },
        syntax::{
            HrtbBinder, ImplItem, RelationMode, SimpleTySet, TraitClause, TraitClauseList,
            TraitParam, TraitSpec, Ty, TyCtxt, TyKind, TyOrRe, TyVisitor, TyVisitorInfallibleExt,
            UniversalTyVar,
        },
    },
    typed_joiner,
    utils::hash::FxHashMap,
};
use std::{convert::Infallible, ops::ControlFlow, rc::Rc};

// === Impl Obligation === //

#[derive(Debug, Clone)]
struct SelectionRejected;

impl<'tcx> ClauseCx<'tcx> {
    pub fn oblige_ty_meets_clauses(
        &mut self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        lhs: Ty,
        rhs: TraitClauseList,
    ) -> MultiPromise<'tcx, TraitClauseError> {
        let s = self.session();

        let mut collector = MultiPromiseBuilder::new();

        for &clause in rhs.r(s) {
            self.oblige_ty_meets_clause(fuel, universe, lhs, clause)
                .join(&mut collector);
        }

        collector.finish()
    }

    pub fn oblige_ty_meets_clause(
        &mut self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        lhs: Ty,
        rhs: TraitClause,
    ) -> Promise<'tcx, TraitClauseError> {
        match rhs {
            TraitClause::Outlives(rhs_dir, rhs) => self
                .oblige_general_outlives(TyOrRe::Ty(lhs), rhs, rhs_dir)
                .map(|_ccx, error| TraitClauseError::Outlives(error)),
            TraitClause::Trait(rhs) => self
                .oblige_ty_meets_trait(fuel, universe.clone(), lhs, rhs)
                .map(|_ccx, error| TraitClauseError::Trait(error)),
        }
    }

    pub fn oblige_ty_meets_trait(
        &mut self,
        fuel: ClauseFuel,
        universe: HrtbUniverse,
        lhs: Ty,
        rhs: HrtbBinder,
    ) -> Promise<'tcx, UninstantiatedTraitImplError> {
        let s = self.session();

        let universe = {
            if rhs.defs.r(s).is_empty() {
                universe
            } else {
                universe.nest(HrtbUniverseInfo {})
            }
        };

        let rhs_instantiated = self.instantiate_hrtb_universal(fuel, universe.clone(), rhs);

        let spec_not_met =
            self.oblige_ty_meets_trait_instantiated(fuel, universe, lhs, rhs_instantiated);

        typed_joiner! {
            let spec_not_met = spec_not_met;

            |ccx| {
                UninstantiatedTraitImplError {
                    lhs,
                    rhs,
                    rhs_instantiated,
                    spec_not_met: spec_not_met.map(|v| v.kind),
                }
            }
        }
    }

    pub fn oblige_ty_meets_trait_instantiated(
        &mut self,
        fuel: ClauseFuel,
        universe: HrtbUniverse,
        lhs: Ty,
        rhs: TraitSpec,
    ) -> Promise<'tcx, InstantiatedTraitImplError> {
        let (promise, handle) = Promise::new();

        self.push_obligation(ClauseObligation::TyMeetsTrait {
            handle,
            fuel: fuel.consume(),
            universe,
            lhs,
            rhs,
        });

        promise
    }

    pub(super) fn run_oblige_ty_meets_trait_instantiated(
        &mut self,
        handle: PromiseHandle<'tcx, InstantiatedTraitImplError>,
        fuel: ClauseFuel,
        universe: HrtbUniverse,
        lhs: Ty,
        rhs: TraitSpec,
    ) -> ObligationResult {
        let s = self.session();

        // Enforce fuel limit.
        if fuel.is_exhausted() {
            self.kill_obligations_with_id(fuel.kill_id());

            handle.reject(
                self,
                InstantiatedTraitImplError {
                    lhs,
                    rhs,
                    kind: InstantiatedTraitImplErrorKind::RecursionLimit,
                },
            );

            return Ok(());
        }

        // See whether the type itself can provide the implementation.
        match *self.ucx().peel_ty_infer_var(lhs).r(s) {
            TyKind::Trait(_re, _muta, clauses) => {
                todo!()
            }
            TyKind::UniversalVar(universal) => {
                let universal_elab =
                    self.elaborate_ty_universal_clauses_possibly_floating(universal);

                match self
                    .clone()
                    .try_select_inherent_impl(fuel, &universe, universal_elab, rhs)?
                {
                    Ok(PromiseValue {
                        value: fork,
                        promise,
                    }) => {
                        *self = fork;

                        promise
                            .map(move |_ccx, error| InstantiatedTraitImplError {
                                lhs,
                                rhs,
                                kind: InstantiatedTraitImplErrorKind::InherentUnsatisfied(error),
                            })
                            .forward(self, handle);

                        return Ok(());
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
                handle.accept(self);

                return Ok(());
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
            handle.reject(
                self,
                InstantiatedTraitImplError {
                    lhs,
                    rhs,
                    kind: InstantiatedTraitImplErrorKind::NoSuitableImpl,
                },
            );

            return Ok(());
        };

        *self = confirmation;

        Ok(())
    }

    fn try_select_inherent_impl(
        self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        lhs: UniversalElaboration,
        rhs: TraitSpec,
    ) -> ObligationResult<
        Result<PromiseValue<'tcx, Self, InherentImplUnsatisfiedError>, SelectionRejected>,
    > {
        let s = self.session();

        let reified_var_roots = lhs.collect_roots_if_floating(&self);

        for &lhs in lhs.clauses.r(s) {
            let TraitClause::Trait(lhs) = lhs else {
                continue;
            };

            if lhs.inner.def != rhs.def {
                continue;
            }

            if let Ok(promise) = self.clone().try_select_single_inherent_impl(
                fuel,
                universe,
                lhs,
                rhs,
                reified_var_roots.as_ref(),
            )? {
                return Ok(Ok(promise));
            }
        }

        Ok(Err(SelectionRejected))
    }

    fn try_select_single_inherent_impl(
        mut self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        lhs: HrtbBinder,
        rhs: TraitSpec,
        reified_var_roots: Option<&WipReificationRootSet>,
    ) -> ObligationResult<
        Result<PromiseValue<'tcx, Self, InherentImplUnsatisfiedError>, SelectionRejected>,
    > {
        let s = self.session();

        assert_eq!(lhs.inner.def, rhs.def);

        let is_ready_if_selected =
            self.is_elaborated_clause_ready_if_selected(reified_var_roots, lhs);

        let mut culprits = MultiPromiseBuilder::new();

        // Instantiate the current clause existentially and match its elaborated parameters against
        // our specification.
        let lhs_orig = lhs;
        let lhs = self.instantiate_hrtb_infer(cause.clone(), universe.clone(), lhs);

        let mut param_iter = lhs.params.r(s).iter().zip(rhs.params.r(s)).enumerate();

        for (idx, (&lhs_param, &rhs_param)) in
            (&mut param_iter).take(*rhs.def.r(s).regular_generic_count as usize)
        {
            let TraitParam::Equals(lhs) = lhs_param else {
                unreachable!();
            };

            match rhs_param {
                TraitParam::Equals(rhs) => match (lhs, rhs) {
                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                        // This can be an obligation because selection shouldn't depend on regions.
                        self.oblige_re_outlives_re(lhs, rhs, RelationMode::Equate)
                            .map(move |_ccx, error| {
                                InherentImplErrorImplCulprit::RegionEquate(idx as u32, error)
                            })
                            .join(&mut culprits);
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        // See whether we can reject this parameter.
                        match self
                            .ucx_mut()
                            .unify_ty_and_ty(lhs, rhs, RelationMode::Equate)
                        {
                            Ok(promise) => promise
                                .map(move |_ccx, error| {
                                    InherentImplErrorImplCulprit::TyEquateRegion(idx as u32, error)
                                })
                                .join(&mut culprits),
                            Err(_err) => {
                                return Ok(Err(SelectionRejected));
                            }
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
        for (idx, (&lhs_param, &rhs_param)) in param_iter {
            let TraitParam::Equals(lhs) = lhs_param else {
                unreachable!();
            };

            match rhs_param {
                TraitParam::Equals(rhs) => match (lhs, rhs) {
                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                        self.oblige_re_outlives_re(lhs, rhs, RelationMode::Equate)
                            .map(move |_ccx, error| {
                                InherentImplErrorImplCulprit::RegionEquate(idx as u32, error)
                            })
                            .join(&mut culprits);
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        self.oblige_ty_unifies_ty(lhs, rhs, RelationMode::Equate)
                            .map(move |_ccx, error| {
                                InherentImplErrorImplCulprit::TyEquate(idx as u32, error)
                            })
                            .join(&mut culprits);
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(rhs) => match lhs {
                    TyOrRe::Re(lhs) => {
                        // TODO
                        self.oblige_re_meets_clauses(lhs, rhs)
                            .map(move |_ccx, error| {
                                InherentImplErrorImplCulprit::TyEquate(idx as u32, error)
                            })
                            .join(&mut culprits);
                    }
                    TyOrRe::Ty(lhs) => {
                        // TODO
                        self.oblige_ty_meets_clauses(fuel, universe, lhs, rhs);
                    }
                },
            }
        }

        let promise = culprits
            .finish()
            .map(|_ccx, culprits| InherentImplUnsatisfiedError {
                lhs: lhs_orig,
                rhs,
                culprits,
            });

        Ok(Ok(promise.and_value(self)))
    }

    fn try_select_block_impl(
        mut self,
        universe: &HrtbUniverse,
        lhs: Ty,
        rhs: Obj<ImplItem>,
        spec: TraitSpec,
    ) -> Result<PromiseValue<'tcx, Self, BlockImplUnsatisfiedError>, SelectionRejected> {
        let s = self.session();

        let mut collector = MultiPromiseBuilder::new();

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
        match self
            .ucx_mut()
            .unify_ty_and_ty(lhs, target_ty, RelationMode::Equate)
        {
            Ok(promise) => {
                // TODO: Handle promise!!!
            }
            Err(_err) => return Err(SelectionRejected),
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
                        // TODO: Handle promise!!!
                        self.ucx_mut()
                            .unify_re_and_re(instance, required, RelationMode::Equate);
                    }
                    (TyOrRe::Ty(instance), TyOrRe::Ty(required)) => {
                        match self.ucx_mut().unify_ty_and_ty(
                            instance,
                            required,
                            RelationMode::Equate,
                        ) {
                            Ok(promise) => {
                                // TODO: Handle promise
                            }
                            Err(_) => return Err(SelectionRejected),
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

        let promise = collector
            .finish()
            .map(move |_ccx, culprits| BlockImplUnsatisfiedError {
                block: rhs,
                culprits,
            });

        Ok(promise.and_value(self))
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

            match self.ucx_mut().unify_ty_and_ty(
                rhs_input,
                tcx.intern(TyKind::Tuple(sig.args)),
                RelationMode::Equate,
            ) {
                Ok(promise) => {
                    // TODO: Handle promise!!!
                }
                Err(_) => return Err(SelectionRejected),
            }

            match self
                .ucx_mut()
                .unify_ty_and_ty(rhs_output, sig.ret_ty, RelationMode::Equate)
            {
                Ok(promise) => {
                    // TODO: Handle promise!!!
                }
                Err(_) => {
                    return Err(SelectionRejected);
                }
            }

            return Ok(self);
        }

        Err(SelectionRejected)
    }
}

// === Cover Obligation === //

impl<'tcx> ClauseCx<'tcx> {
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
        handle: PromiseHandle<'tcx, NotCoveredError>,
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
