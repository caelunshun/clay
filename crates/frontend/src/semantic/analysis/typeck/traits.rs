use crate::{
    base::{
        Diag,
        arena::{LateInit, Obj},
    },
    semantic::{
        analysis::{
            BinderSubstitution, InferCx, SubstitutionFolder, TyAndTyRelateError, TyCtxt,
            TyFolderInfallible as _,
        },
        syntax::{
            AnyGeneric, GenericBinder, GenericSolveStep, ImplDef, ListOfTraitClauseList, Re,
            RelationMode, SpannedRe, SpannedTraitClauseList, SpannedTraitClauseView,
            SpannedTraitParamView, SpannedTraitSpec, SpannedTy, SpannedTyOrReView, SpannedTyView,
            TraitClause, TraitParam, TraitSpec, Ty, TyKind, TyOrRe, TyOrReList,
        },
    },
};
use index_vec::{IndexVec, define_index_type};

// === Errors === //

#[derive(Debug, Clone)]
pub struct TyAndClauseRelateError {
    pub lhs: SpannedTy,
    pub rhs: SpannedTraitClauseList,
    pub errors: Vec<(u32, Box<TyAndTraitRelateError>)>,
    pub had_ambiguity: bool,
}

#[derive(Debug, Clone)]
#[must_use]
pub enum TyAndTraitRelateResolution {
    Impl(TyAndImplResolution),
    Inherent,
}

#[derive(Debug, Clone)]
pub struct TyAndTraitRelateError {
    pub lhs: SpannedTy,
    pub rhs: SpannedTraitSpec,
    pub resolutions: Vec<TyAndImplResolution>,
    pub rejections: Vec<Box<TyAndImplRelateError>>,
    pub had_ambiguity: bool,
}

#[derive(Debug, Clone)]
pub struct TyAndImplResolution {
    pub impl_def: Obj<ImplDef>,
    pub impl_generics: TyOrReList,
}

#[derive(Debug, Clone)]
pub struct TyAndImplRelateError {
    pub lhs: SpannedTy,
    pub rhs: Obj<ImplDef>,
    pub bad_target: Option<Box<TyAndTyRelateError>>,
    pub bad_trait_args: Vec<(u32, Box<TyAndTyRelateError>)>,
    pub bad_trait_clauses: Vec<TyAndImplGenericClauseError>,
    pub bad_trait_assoc_types: Vec<(u32, TyAndImplAssocRelateError)>,
    pub had_ambiguity: bool,
}

#[derive(Debug, Clone)]
pub struct TyAndImplGenericClauseError {
    pub step: GenericSolveStep,
    pub error: Box<TyAndClauseRelateError>,
}

#[derive(Debug, Clone)]
pub enum TyAndImplAssocRelateError {
    TyAndTy(Box<TyAndTyRelateError>),
    TyAndClause(Box<TyAndClauseRelateError>),
}

#[derive(Debug, Clone)]
pub struct RelateClauseAndTraitError;

// === Order Solving === //

impl TyCtxt {
    pub fn determine_impl_generic_solve_order(&self, def: Obj<ImplDef>) {
        let s = &self.session;

        define_index_type! {
            struct GenericIdx = u32;
        }

        define_index_type! {
            struct ClauseIndex = u32;
        }

        struct GenericState {
            covered: bool,
            deps: Vec<ClauseIndex>,
        }

        struct ClauseState {
            blockers: u32,
            step_idx: GenericSolveStep,
            spec: TraitSpec,
        }

        let generic_defs = &def.r(s).generics.r(s).generics;

        // Populate clauses
        let mut generic_states = generic_defs
            .iter()
            .map(|_| GenericState {
                covered: false,
                deps: Vec::new(),
            })
            .collect::<IndexVec<GenericIdx, _>>();

        let mut clause_states = IndexVec::<ClauseIndex, ClauseState>::new();

        for (step_generic_idx, main_generic_def) in generic_defs.iter().enumerate() {
            for (step_clause_idx, clause_def) in
                main_generic_def.clauses(s).value.r(s).iter().enumerate()
            {
                let TraitClause::Trait(spec) = *clause_def else {
                    continue;
                };

                let clause_state_idx = clause_states.next_idx();
                let mut blockers = 1;

                generic_states[main_generic_def.binder(s).idx as usize]
                    .deps
                    .push(clause_state_idx);

                for &param in &spec.params.r(s)[..spec.def.r(s).regular_generic_count as usize] {
                    let TraitParam::Equals(ty) = param else {
                        unreachable!()
                    };

                    cbit::cbit!(for generic in self.mentioned_generics(ty) {
                        debug_assert_eq!(generic.binder(s).def, def.r(s).generics);

                        generic_states[generic.binder(s).idx as usize]
                            .deps
                            .push(clause_state_idx);

                        blockers += 1;
                    });
                }

                clause_states.push(ClauseState {
                    step_idx: GenericSolveStep {
                        generic_idx: step_generic_idx as u32,
                        clause_idx: step_clause_idx as u32,
                    },
                    blockers,
                    spec,
                });
            }
        }

        // Iteratively mark covered generics.
        let mut solve_queue = Vec::new();
        let mut solve_order = Vec::new();

        fn cover_idx(
            solve_queue: &mut Vec<TraitSpec>,
            solve_order: &mut Vec<GenericSolveStep>,
            generic_states: &mut IndexVec<GenericIdx, GenericState>,
            clause_states: &mut IndexVec<ClauseIndex, ClauseState>,
            idx: GenericIdx,
        ) {
            let generic = &mut generic_states[idx];

            if generic.covered {
                return;
            }

            generic.covered = true;

            for &dep in &generic.deps {
                let clause = &mut clause_states[dep];
                clause.blockers -= 1;

                if clause.blockers > 0 {
                    continue;
                }

                solve_queue.push(clause.spec);
                solve_order.push(clause.step_idx);
            }
        }

        fn cover_ty(
            tcx: &TyCtxt,
            solve_queue: &mut Vec<TraitSpec>,
            solve_order: &mut Vec<GenericSolveStep>,
            generic_states: &mut IndexVec<GenericIdx, GenericState>,
            clause_states: &mut IndexVec<ClauseIndex, ClauseState>,
            binder: Obj<GenericBinder>,
            ty: Ty,
        ) {
            let s = &tcx.session;

            cbit::cbit!(for generic in tcx.mentioned_generics(TyOrRe::Ty(ty)) {
                debug_assert_eq!(generic.binder(s).def, binder);

                cover_idx(
                    solve_queue,
                    solve_order,
                    generic_states,
                    clause_states,
                    GenericIdx::from_raw(generic.binder(s).idx),
                );
            });
        }

        // Cover generics appearing in the target type and trait.
        cover_ty(
            self,
            &mut solve_queue,
            &mut solve_order,
            &mut generic_states,
            &mut clause_states,
            def.r(s).generics,
            def.r(s).target.value,
        );

        if let Some(trait_) = def.r(s).trait_ {
            for &param in trait_.value.params.r(s) {
                match param {
                    TyOrRe::Re(param) => {
                        match param {
                            Re::Gc => {
                                // (nothing mentioned)
                            }
                            Re::Universal(param) => {
                                cover_idx(
                                    &mut solve_queue,
                                    &mut solve_order,
                                    &mut generic_states,
                                    &mut clause_states,
                                    GenericIdx::from_raw(param.r(s).binder.idx),
                                );
                            }
                            Re::InferVar(_) | Re::ExplicitInfer | Re::Erased => unreachable!(),
                        }
                    }
                    TyOrRe::Ty(param) => {
                        cover_ty(
                            self,
                            &mut solve_queue,
                            &mut solve_order,
                            &mut generic_states,
                            &mut clause_states,
                            def.r(s).generics,
                            param,
                        );
                    }
                }
            }
        }

        // Recursively uncover more generics.
        while let Some(clause) = solve_queue.pop() {
            for param in &clause.params.r(s)[(clause.def.r(s).regular_generic_count as usize)..] {
                match param {
                    TraitParam::Equals(eq) => {
                        // We can use this to reveal more equalities!
                        cover_ty(
                            self,
                            &mut solve_queue,
                            &mut solve_order,
                            &mut generic_states,
                            &mut clause_states,
                            def.r(s).generics,
                            eq.unwrap_ty(),
                        );
                    }
                    TraitParam::Unspecified(_) => {
                        // (does not contribute to solve order)
                    }
                }
            }
        }

        // Ensure that all generics are covered.
        for (state, def) in generic_states.iter().zip(generic_defs) {
            if !state.covered {
                Diag::span_err(def.span(s), "generic parameter not covered by `impl`").emit();
            }
        }

        LateInit::init(&def.r(s).generic_solve_order, solve_order);
    }
}

// === Inference Context === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
struct ImplFreshInfer {
    target: Ty,
    trait_: TyOrReList,
    impl_generics: TyOrReList,
    impl_generic_clauses: ListOfTraitClauseList,
}

impl InferCx<'_> {
    fn instantiate_fresh_impl_vars(&mut self, candidate: Obj<ImplDef>) -> ImplFreshInfer {
        let tcx = self.tcx();
        let s = self.session();

        // Define fresh variables describing the substitutions to be made.
        let binder = candidate.r(s).generics;
        let impl_generics = binder
            .r(s)
            .generics
            .iter()
            .map(|generic| match generic {
                AnyGeneric::Re(_) => TyOrRe::Re(self.fresh_re()),
                AnyGeneric::Ty(_) => TyOrRe::Ty(self.fresh_ty()),
            })
            .collect::<Vec<_>>();

        let impl_generics = tcx.intern_ty_or_re_list(&impl_generics);
        let substs = BinderSubstitution {
            binder,
            substs: impl_generics,
        };

        // Substitute the target type
        let target = SubstitutionFolder::new(tcx, tcx.intern_ty(TyKind::This), substs)
            .fold_ty(candidate.r(s).target.value);

        // Substitute inference clauses
        let inf_var_clauses = binder
            .r(s)
            .generics
            .iter()
            .map(|generic| {
                let clauses = match generic {
                    AnyGeneric::Re(generic) => generic.r(s).clauses.value,
                    AnyGeneric::Ty(generic) => generic.r(s).user_clauses.value,
                };

                SubstitutionFolder::new(tcx, target, substs).fold_clause_list(clauses)
            })
            .collect::<Vec<_>>();

        let impl_generic_clauses = tcx.intern_list_of_trait_clause_list(&inf_var_clauses);

        let trait_ = SubstitutionFolder::new(tcx, target, substs)
            .fold_ty_or_re_list(candidate.r(s).trait_.unwrap().value.params);

        ImplFreshInfer {
            target,
            trait_,
            impl_generics,
            impl_generic_clauses,
        }
    }

    pub fn relate_ty_and_clause(
        &mut self,
        lhs: SpannedTy,
        rhs: SpannedTraitClauseList,
        binder: &mut GenericBinder,
    ) -> Result<(), Box<TyAndClauseRelateError>> {
        let tcx = self.tcx();
        let s = self.session();

        let mut fork = self.clone();

        let mut error = TyAndClauseRelateError {
            lhs,
            rhs,
            errors: Vec::new(),
            had_ambiguity: false,
        };

        for (idx, clause) in rhs.iter(s).enumerate() {
            match clause.view(tcx) {
                SpannedTraitClauseView::Outlives(rhs) => {
                    fork.relate_ty_and_re(lhs, rhs);
                }
                SpannedTraitClauseView::Trait(rhs) => {
                    if let Err(err) = fork.relate_ty_and_trait(lhs, rhs, binder) {
                        error.had_ambiguity |= err.had_ambiguity;
                        error.errors.push((idx as u32, err));
                    }
                }
            }
        }

        if error.had_ambiguity || !error.errors.is_empty() {
            return Err(Box::new(error));
        }

        *self = fork;

        Ok(())
    }

    pub fn relate_re_and_clause(&mut self, lhs: SpannedRe, rhs: SpannedTraitClauseList) {
        let tcx = self.tcx();
        let s = self.session();

        for clause in rhs.iter(s) {
            match clause.view(tcx) {
                SpannedTraitClauseView::Outlives(rhs) => {
                    self.relate_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs);
                }
                SpannedTraitClauseView::Trait(_) => {
                    unreachable!()
                }
            }
        }
    }

    pub fn relate_ty_and_trait(
        &mut self,
        lhs: SpannedTy,
        rhs: SpannedTraitSpec,
        binder: &mut GenericBinder,
    ) -> Result<TyAndTraitRelateResolution, Box<TyAndTraitRelateError>> {
        let tcx = self.tcx();
        let s = self.session();

        // See whether the type itself can provide the implementation.
        match self.try_peel_ty_var(lhs).view(tcx) {
            SpannedTyView::Trait(clauses) => {
                todo!()
            }
            SpannedTyView::Universal(generic) => {
                match self.relate_clause_and_trait(
                    tcx.elaborate_generic_clauses(generic, binder),
                    rhs.value,
                    binder,
                ) {
                    Ok(()) => {
                        return Ok(TyAndTraitRelateResolution::Inherent);
                    }
                    Err(RelateClauseAndTraitError) => {
                        // (fallthrough)
                    }
                }
            }
            _ => {
                // (no other types can inherently fulfill a trait requirement without an `impl`)
            }
        }

        // Otherwise, attempt to provide the implementation through an implementation block.
        let mut error = TyAndTraitRelateError {
            lhs,
            rhs,
            resolutions: Vec::new(),
            rejections: Vec::new(),
            had_ambiguity: false,
        };

        let mut accepted_fork = None;

        for &candidate in rhs.value.def.r(s).impls.read().iter() {
            let mut fork = self.clone();

            match fork.relate_ty_and_impl_no_fork(lhs, candidate, rhs, binder) {
                Ok(resolution) => {
                    error.resolutions.push(resolution);
                    accepted_fork = Some(fork);
                }
                Err(rejection) => {
                    error.had_ambiguity |= rejection.had_ambiguity;
                    error.rejections.push(rejection);
                }
            }
        }

        if error.resolutions.len() > 1 {
            error.had_ambiguity = true;
        }

        if error.had_ambiguity || error.resolutions.is_empty() {
            return Err(Box::new(error));
        }

        *self = accepted_fork.unwrap();

        Ok(TyAndTraitRelateResolution::Impl(
            error.resolutions.into_iter().next().unwrap(),
        ))
    }

    fn relate_ty_and_impl_no_fork(
        &mut self,
        lhs: SpannedTy,
        rhs: Obj<ImplDef>,
        spec: SpannedTraitSpec,
        binder: &mut GenericBinder,
    ) -> Result<TyAndImplResolution, Box<TyAndImplRelateError>> {
        let s = self.session();
        let tcx = self.tcx();

        let mut error = TyAndImplRelateError {
            lhs,
            rhs,
            bad_target: None,
            bad_trait_args: Vec::new(),
            bad_trait_clauses: Vec::new(),
            bad_trait_assoc_types: Vec::new(),
            had_ambiguity: false,
        };

        // Replace universal qualifications in `impl` with inference variables
        let rhs_fresh = self.instantiate_fresh_impl_vars(rhs);

        // See whether our target type can even match this `impl` block.
        if let Err(err) = self.relate_ty_and_ty(
            lhs,
            // We don't really care about the spans of types outside our main body so this is
            // okay for diagnostics.
            SpannedTy::new_unspanned(rhs_fresh.target),
            RelationMode::Equate,
        ) {
            error.bad_target = Some(err);
        }

        // See whether our specific target trait clauses can be covered by the inferred
        // generics. We only check the regular generics at this stage since associated types are
        // defined entirely from our solved regular generics.
        for (idx, (&instance, required_param)) in rhs_fresh
            .trait_
            .r(s)
            .iter()
            .zip(spec.view(tcx).params.iter(s))
            .take(spec.value.def.r(s).regular_generic_count as usize)
            .enumerate()
        {
            match required_param.view(tcx) {
                SpannedTraitParamView::Equals(required) => {
                    match (instance, required.view(tcx)) {
                        (TyOrRe::Re(instance), SpannedTyOrReView::Re(required)) => {
                            self.relate_re_and_re(
                                // We don't really care about the spans of types outside our main body
                                // so this is okay for diagnostics.
                                SpannedRe::new_unspanned(instance),
                                required,
                                RelationMode::Equate,
                            );
                        }
                        (TyOrRe::Ty(instance), SpannedTyOrReView::Ty(required)) => {
                            if let Err(err) = self.relate_ty_and_ty(
                                // We don't really care about the spans of types outside our main body
                                // so this is okay for diagnostics.
                                SpannedTy::new_unspanned(instance),
                                required,
                                RelationMode::Equate,
                            ) {
                                error.bad_trait_args.push((idx as u32, err));
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                SpannedTraitParamView::Unspecified(_) => {
                    unreachable!()
                }
            }
        }

        // Skip nested trait checks if we failed to match the target since...
        //
        // a) it causes unnecessary ambiguities
        // b) it can cause trait-check overflows which could otherwise be avoided
        // c) it's not even needed for diagnostics
        //
        if error.bad_target.is_none() && error.bad_trait_args.is_empty() {
            // See whether the inferences we made for all our variables are valid.
            // See `ImplDef::generic_solve_order` on why the specific solving order is important.
            for &infer_step in rhs.r(s).generic_solve_order.iter() {
                let var = rhs_fresh.impl_generics.r(s)[infer_step.generic_idx as usize];
                let clause = rhs_fresh.impl_generic_clauses.r(s)[infer_step.generic_idx as usize]
                    .r(s)[infer_step.clause_idx as usize];

                let clause = tcx.intern_trait_clause_list(&[clause]);

                match var {
                    TyOrRe::Re(re) => {
                        self.relate_re_and_clause(
                            // We don't really care about the spans of types outside our main body
                            // so this is okay for diagnostics.
                            SpannedRe::new_unspanned(re),
                            // Same here.
                            SpannedTraitClauseList::new_unspanned(clause),
                        );
                    }
                    TyOrRe::Ty(ty) => {
                        if let Err(err) = self.relate_ty_and_clause(
                            // We don't really care about the spans of types outside our main body
                            // so this is okay for diagnostics.
                            SpannedTy::new_unspanned(ty),
                            // Same here.
                            SpannedTraitClauseList::new_unspanned(clause),
                            binder,
                        ) {
                            error.had_ambiguity |= err.had_ambiguity;
                            error.bad_trait_clauses.push(TyAndImplGenericClauseError {
                                step: infer_step,
                                error: err,
                            });
                        }
                    }
                }
            }

            // See whether the user-supplied associated type constraints match what we inferred.
            for (idx, (&instance_ty, required_param)) in rhs_fresh
                .trait_
                .r(s)
                .iter()
                .zip(spec.view(tcx).params.iter(s))
                .enumerate()
                .skip(spec.value.def.r(s).regular_generic_count as usize)
            {
                // Associated types are never regions.
                let instance_ty = instance_ty.unwrap_ty();

                match required_param.view(tcx) {
                    SpannedTraitParamView::Equals(required_ty) => {
                        let SpannedTyOrReView::Ty(required_ty) = required_ty.view(tcx) else {
                            unreachable!()
                        };

                        if let Err(err) = self.relate_ty_and_ty(
                            SpannedTy::new_unspanned(instance_ty),
                            required_ty,
                            RelationMode::Equate,
                        ) {
                            error
                                .bad_trait_assoc_types
                                .push((idx as u32, TyAndImplAssocRelateError::TyAndTy(err)));
                        }
                    }
                    SpannedTraitParamView::Unspecified(additional_clauses) => {
                        if let Err(err) = self.relate_ty_and_clause(
                            SpannedTy::new_unspanned(instance_ty),
                            additional_clauses,
                            binder,
                        ) {
                            error.had_ambiguity |= err.had_ambiguity;
                            error
                                .bad_trait_assoc_types
                                .push((idx as u32, TyAndImplAssocRelateError::TyAndClause(err)));
                        }
                    }
                }
            }
        }

        // Do some error checking.
        if error.had_ambiguity
            || error.bad_target.is_some()
            || !error.bad_trait_args.is_empty()
            || !error.bad_trait_clauses.is_empty()
            || !error.bad_trait_assoc_types.is_empty()
        {
            return Err(Box::new(error));
        }

        Ok(TyAndImplResolution {
            impl_def: rhs,
            impl_generics: rhs_fresh.impl_generics,
        })
    }

    fn relate_clause_and_trait(
        &mut self,
        lhs_elaborated: SpannedTraitClauseList,
        rhs: TraitSpec,
        binder: &mut GenericBinder,
    ) -> Result<(), RelateClauseAndTraitError> {
        let s = self.session();
        let tcx = self.tcx();

        // Find the clause that could prove our trait.
        let lhs = lhs_elaborated.iter(s).find(|clause| match clause.value {
            TraitClause::Outlives(_) => false,
            TraitClause::Trait(lhs) => lhs.def == rhs.def,
        });

        let Some(lhs) = lhs else {
            return Err(RelateClauseAndTraitError {});
        };

        let SpannedTraitClauseView::Trait(lhs) = lhs.view(tcx) else {
            unreachable!()
        };

        let mut fork = self.clone();

        for (lhs_param, &rhs_param) in lhs.view(tcx).params.iter(s).zip(rhs.params.r(s)) {
            let SpannedTraitParamView::Equals(lhs) = lhs_param.view(tcx) else {
                unreachable!();
            };

            match rhs_param {
                TraitParam::Equals(rhs) => match (lhs.view(tcx), rhs) {
                    (SpannedTyOrReView::Re(lhs), TyOrRe::Re(rhs)) => {
                        fork.relate_re_and_re(
                            lhs,
                            SpannedRe::new_unspanned(rhs),
                            RelationMode::Equate,
                        );
                    }
                    (SpannedTyOrReView::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        if let Err(_err) = fork.relate_ty_and_ty(
                            lhs,
                            SpannedTy::new_unspanned(rhs),
                            RelationMode::Equate,
                        ) {
                            return Err(RelateClauseAndTraitError);
                        }
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(rhs_clauses) => {
                    let SpannedTyOrReView::Ty(lhs) = lhs.view(tcx) else {
                        unreachable!()
                    };

                    if let Err(_err) = fork.relate_ty_and_clause(
                        lhs,
                        SpannedTraitClauseList::new_unspanned(rhs_clauses),
                        binder,
                    ) {
                        return Err(RelateClauseAndTraitError);
                    }
                }
            }
        }

        *self = fork;

        Ok(())
    }
}
