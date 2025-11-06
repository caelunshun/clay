use crate::{
    base::{
        Diag,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    symbol,
    typeck::{
        analysis::TyCtxt,
        syntax::{
            AnyGeneric, GenericBinder, GenericInstance, GenericSolveStep, ImplDef, InferTyVar,
            ListOfTraitClauseList, Re, TraitClause, TraitClauseList, TraitParam, TraitSpec, Ty,
            TyKind, TyOrRe, TyOrReList, TypeGeneric,
        },
    },
};
use disjoint::DisjointSetVec;
use index_vec::{IndexVec, define_index_type};

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
        let mut step_clause_idx = 0;

        for (step_generic_idx, main_generic_def) in
            generic_defs.iter().filter_map(|v| v.as_ty()).enumerate()
        {
            for clause_def in main_generic_def.r(s).user_clauses.r(s) {
                let TraitClause::Trait(spec) = *clause_def else {
                    continue;
                };

                let clause_state_idx = clause_states.next_idx();
                let mut blockers = 1;

                generic_states[main_generic_def.r(s).binder.idx as usize]
                    .deps
                    .push(clause_state_idx);

                for &param in &spec.params.r(s)[..spec.def.r(s).regular_generic_count as usize] {
                    let TraitParam::Equals(ty) = param else {
                        unreachable!()
                    };

                    cbit::cbit!(for generic in self.mentioned_generics(ty) {
                        let Some(generic) = generic.as_ty() else {
                            continue;
                        };

                        debug_assert_eq!(generic.r(s).binder.def, def.r(s).generics);

                        generic_states[generic.r(s).binder.idx as usize]
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

                step_clause_idx += 1;
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
                let Some(generic) = generic.as_ty() else {
                    continue;
                };

                debug_assert_eq!(generic.r(s).binder.def, binder);

                cover_idx(
                    solve_queue,
                    solve_order,
                    generic_states,
                    clause_states,
                    GenericIdx::from_raw(generic.r(s).binder.idx),
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
            def.r(s).target,
        );

        if let Some(trait_) = def.r(s).trait_ {
            for param in trait_.params.r(s).iter().filter_map(|v| v.as_ty()) {
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

    pub fn instantiate_generic_clauses(
        &self,
        generic: Obj<TypeGeneric>,
        binder: &mut GenericBinder,
    ) -> TraitClauseList {
        let s = &self.session;

        let generic = generic.r(s);

        if let Some(v) = LateInit::get(&generic.instantiated_clauses) {
            return *v;
        }

        let clauses = generic
            .user_clauses
            .r(s)
            .iter()
            .map(|clause| match *clause {
                TraitClause::Outlives(re) => TraitClause::Outlives(re),
                TraitClause::Trait(spec) => {
                    let params = spec
                        .params
                        .r(s)
                        .iter()
                        .zip(&spec.def.r(s).generics.r(s).generics)
                        .map(|(&param, def)| {
                            let clauses = match param {
                                TraitParam::Equals(_) => return param,
                                TraitParam::Unspecified(clauses) => self.join_trait_clause_lists(
                                    // TODO: These require some substitutions and super-traits
                                    //  should be revealed.
                                    *def.unwrap_ty().r(s).user_clauses,
                                    clauses,
                                ),
                            };

                            // TODO: Better debug names.
                            let generic = Obj::new(
                                TypeGeneric {
                                    span: Span::DUMMY,
                                    ident: Ident {
                                        span: Span::DUMMY,
                                        text: symbol!("?"),
                                        raw: false,
                                    },
                                    binder: LateInit::uninit(),
                                    user_clauses: LateInit::new(clauses),
                                    instantiated_clauses: LateInit::uninit(),
                                    is_synthetic: true,
                                },
                                s,
                            );

                            binder.generics.push(AnyGeneric::Ty(generic));

                            TraitParam::Equals(TyOrRe::Ty(
                                self.intern_ty(TyKind::Universal(generic)),
                            ))
                        })
                        .collect::<Vec<_>>();

                    TraitClause::Trait(TraitSpec {
                        def: spec.def,
                        params: self.intern_trait_param_list(&params),
                    })
                }
            })
            .collect::<Vec<_>>();

        let clauses = self.intern_trait_clause_list(&clauses);

        LateInit::init(&generic.instantiated_clauses, clauses);

        clauses
    }

    pub fn instantiate_fresh_target_infers(
        &self,
        candidate: Obj<ImplDef>,
        min_infer_var: InferTyVar,
    ) -> ImplFreshInfer {
        let s = &self.session;

        self.queries
            .instantiate_fresh_target_infers
            .compute_infallible((candidate, min_infer_var), |_| {
                let mut min_infer_var = min_infer_var;

                // Define fresh variables describing the substitutions to be made.
                let binder = candidate.r(s).generics;
                let substs = binder
                    .r(s)
                    .generics
                    .iter()
                    .map(|generic| match generic {
                        AnyGeneric::Re(_) => TyOrRe::Re(Re::Erased),
                        AnyGeneric::Ty(generic) => {
                            let ty = self.intern_ty(TyKind::InferVar(min_infer_var, *generic));
                            min_infer_var.0 += 1;

                            TyOrRe::Ty(ty)
                        }
                    })
                    .collect::<Vec<_>>();

                let substs = self.intern_ty_or_re_list(&substs);
                let substs = GenericInstance { binder, substs };

                // Substitute the target type
                let target =
                    self.substitute_ty(candidate.r(s).target, self.intern_ty(TyKind::This), substs);

                let inf_var_clauses = binder
                    .r(s)
                    .generics
                    .iter()
                    .filter_map(|generic| match generic {
                        AnyGeneric::Re(_generic) => None,
                        AnyGeneric::Ty(generic) => Some(self.substitute_clause_list(
                            *generic.r(s).user_clauses,
                            target,
                            substs,
                        )),
                    })
                    .collect::<Vec<_>>();

                let inf_var_clauses = self.intern_list_of_trait_clause_list(&inf_var_clauses);

                let trait_instance = self.substitute_ty_or_re_list(
                    candidate.r(s).trait_.unwrap().params,
                    target,
                    substs,
                );

                ImplFreshInfer {
                    target,
                    trait_instance,
                    inf_var_clauses,
                }
            })
    }

    pub fn check_type_assignability_erase_regions(
        &self,
        lhs: Ty,
        rhs: Ty,
        infer_var_inferences: &mut InferVarInferences,
        failures: &mut Vec<SatisfiabilityFailure>,
    ) {
        let s = &self.session;

        if lhs == rhs {
            // The types are compatible!
            return;
        }

        match (*lhs.r(s), *rhs.r(s)) {
            (TyKind::This, _)
            | (_, TyKind::This)
            | (TyKind::ExplicitInfer, _)
            | (_, TyKind::ExplicitInfer) => unreachable!(),
            (TyKind::Reference(_, lhs), TyKind::Reference(_, rhs)) => {
                self.check_type_assignability_erase_regions(
                    lhs,
                    rhs,
                    infer_var_inferences,
                    failures,
                );
            }
            (TyKind::Adt(lhs_def, lhs_args), TyKind::Adt(rhs_def, rhs_args))
                if lhs_def == rhs_def =>
            {
                for (&lhs, &rhs) in lhs_args.r(s).iter().zip(rhs_args.r(s)) {
                    let (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) = (lhs, rhs) else {
                        continue;
                    };

                    self.check_type_assignability_erase_regions(
                        lhs,
                        rhs,
                        infer_var_inferences,
                        failures,
                    );
                }
            }
            (TyKind::Tuple(lhs), TyKind::Tuple(rhs)) if lhs.r(s).len() == rhs.r(s).len() => {
                for (&lhs, &rhs) in lhs.r(s).iter().zip(rhs.r(s)) {
                    self.check_type_assignability_erase_regions(
                        lhs,
                        rhs,
                        infer_var_inferences,
                        failures,
                    );
                }
            }
            (TyKind::InferVar(lhs_var, _), TyKind::InferVar(rhs_var, _)) => {
                if let (Some(lhs_ty), Some(rhs_ty)) = (
                    infer_var_inferences.lookup(lhs_var),
                    infer_var_inferences.lookup(rhs_var),
                ) {
                    self.check_type_assignability_erase_regions(
                        lhs_ty,
                        rhs_ty,
                        infer_var_inferences,
                        failures,
                    );
                } else {
                    infer_var_inferences.union(lhs_var, rhs_var);
                }
            }
            (TyKind::InferVar(lhs_var, _), _) => {
                if let Some(known_lhs) = infer_var_inferences.lookup(lhs_var) {
                    self.check_type_assignability_erase_regions(
                        known_lhs,
                        rhs,
                        infer_var_inferences,
                        failures,
                    );
                } else {
                    infer_var_inferences.assign(lhs_var, rhs);
                }
            }
            (_, TyKind::InferVar(rhs_var, _)) => {
                if let Some(known_rhs) = infer_var_inferences.lookup(rhs_var) {
                    self.check_type_assignability_erase_regions(
                        lhs,
                        known_rhs,
                        infer_var_inferences,
                        failures,
                    );
                } else {
                    infer_var_inferences.assign(rhs_var, lhs);
                }
            }
            // Omissions okay because of intern equality fast-path and the fact that all lifetimes
            // are erased:
            //
            // - `(Simple, Simple)`
            // - `(FnDef, FnDef)`
            // - `(Universal, Universal)`
            // - `(Trait, Trait)`
            //
            _ => {
                failures.push(SatisfiabilityFailure::Structural { lhs, rhs });
            }
        }
    }

    pub fn check_clause_list_assignability_erase_regions(
        &self,
        lhs: Ty,
        rhs: TraitClauseList,
        binder: &mut GenericBinder,
        inferences: &mut InferVarInferences,
        failures: &mut Vec<SatisfiabilityFailure>,
    ) {
        for &clause in rhs.r(&self.session).iter() {
            match clause {
                TraitClause::Outlives(_) => {
                    // (regions are ignored)
                }
                TraitClause::Trait(rhs) => {
                    self.check_trait_assignability_erase_regions(
                        lhs, rhs, binder, inferences, failures,
                    );
                }
            }
        }
    }

    // FIXME: Multiple traits may be applicable if inference variables are involved in the `lhs`
    //  type or `rhs_params` parameter list. We should report those situations and use the
    //  `ImplDef::generic_solve_order` to ensure that we never unnecessarily create them in nested
    //  inferences.
    pub fn check_trait_assignability_erase_regions(
        &self,
        lhs: Ty,
        rhs: TraitSpec,
        binder: &mut GenericBinder,
        inferences: &mut InferVarInferences,
        failures: &mut Vec<SatisfiabilityFailure>,
    ) {
        let s = &self.session;

        // See whether the type itself can provide the implementation.
        let direct_satisfy_failures = match *lhs.r(s) {
            TyKind::Trait(clauses) => {
                todo!()
            }
            TyKind::Universal(generic) => {
                let lhs_instantiated = self.instantiate_generic_clauses(generic, binder);

                let mut sub_failures = Vec::new();
                let mut sub_inferences = inferences.clone();

                self.check_clause_satisfies_clause_erase_regions(
                    lhs_instantiated,
                    rhs,
                    binder,
                    &mut sub_inferences,
                    &mut sub_failures,
                );

                if sub_failures.is_empty() {
                    *inferences = sub_inferences;
                    return;
                }

                Some(sub_failures)
            }
            _ => None,
        };

        // Otherwise, attempt to provide the implementation through an implementation block.
        let mut impl_failures = Vec::new();

        for &candidate in rhs.def.r(s).impls.read().iter() {
            // Replace universal qualifications in `impl` with inference variables
            let min_infer_var = inferences.next_infer_var();
            let candidate_fresh = self.instantiate_fresh_target_infers(candidate, min_infer_var);

            // Check impl candidate.
            let mut sub_failures = Vec::new();
            let mut sub_inferences = inferences.clone();

            sub_inferences.define_infer_vars(candidate_fresh.inf_var_clauses.r(s).len());

            // See whether our target type can even match this `impl` block.
            self.check_type_assignability_erase_regions(
                lhs,
                candidate_fresh.target,
                &mut sub_inferences,
                &mut sub_failures,
            );

            // See whether our specific target trait clauses can be covered by the inferred
            // generics. We only check the regular generics at this stage since associated types are
            // defined entirely from our solved regular generics.
            for (&instance_ty, &required_param) in candidate_fresh
                .trait_instance
                .r(s)
                .iter()
                .zip(rhs.params.r(s))
                .take(rhs.def.r(s).regular_generic_count as usize)
            {
                let TyOrRe::Ty(instance_ty) = instance_ty else {
                    // (regions are ignored)
                    continue;
                };

                match required_param {
                    TraitParam::Equals(required_ty) => {
                        self.check_type_assignability_erase_regions(
                            instance_ty,
                            required_ty.unwrap_ty(),
                            &mut sub_inferences,
                            &mut sub_failures,
                        );
                    }
                    TraitParam::Unspecified(_) => {
                        unreachable!()
                    }
                }
            }

            // See whether the inferences we made for all our variables are valid.
            // See `ImplDef::generic_solve_order` on why the specific solving order is important.
            for infer_step in candidate.r(s).generic_solve_order.iter() {
                let var_id = InferTyVar(min_infer_var.0 + infer_step.generic_idx);
                let clauses = candidate_fresh.inf_var_clauses.r(s)[infer_step.clause_idx as usize];

                let Some(resolved) = sub_inferences.lookup(var_id) else {
                    // This should only happen if a failure occurred elsewhere because of the
                    // requirements on well-formed traits.
                    debug_assert!(!sub_failures.is_empty());
                    continue;
                };

                self.check_clause_list_assignability_erase_regions(
                    resolved,
                    clauses,
                    binder,
                    &mut sub_inferences,
                    failures,
                );
            }

            // See whether the user-supplied associated type constraints match what we inferred.
            for (&instance_ty, &required_param) in candidate_fresh
                .trait_instance
                .r(s)
                .iter()
                .zip(rhs.params.r(s))
                .skip(rhs.def.r(s).regular_generic_count as usize)
            {
                // Associated types are never regions.
                let instance_ty = instance_ty.unwrap_ty();

                match required_param {
                    TraitParam::Equals(required_ty) => {
                        self.check_type_assignability_erase_regions(
                            instance_ty,
                            required_ty.unwrap_ty(),
                            &mut sub_inferences,
                            &mut sub_failures,
                        );
                    }
                    TraitParam::Unspecified(additional_clauses) => {
                        self.check_clause_list_assignability_erase_regions(
                            instance_ty,
                            additional_clauses,
                            binder,
                            &mut sub_inferences,
                            &mut sub_failures,
                        );
                    }
                }
            }

            // If the impl match was successful, commit the inferences and stop scanning for more
            // candidates. Otherwise, report the failure and continue scanning.
            if sub_failures.is_empty() {
                *inferences = sub_inferences;
                return;
            }

            impl_failures.push(ImplFailure {
                impl_: candidate,
                cause: sub_failures,
            });
        }

        failures.push(SatisfiabilityFailure::CannotSatisfy {
            lhs,
            rhs,
            direct_satisfy_failures,
            impl_failures,
        });
    }

    pub fn check_clause_satisfies_clause_erase_regions(
        &self,
        lhs_instantiated: TraitClauseList,
        rhs: TraitSpec,
        binder: &mut GenericBinder,
        inferences: &mut InferVarInferences,
        failures: &mut Vec<SatisfiabilityFailure>,
    ) {
        let s = &self.session;

        let mut direct_failures = Vec::new();

        for &lhs in lhs_instantiated.r(s).iter() {
            match lhs {
                TraitClause::Outlives(_) => {
                    // (regions are ignored)
                }
                TraitClause::Trait(lhs) => {
                    if lhs.def != rhs.def {
                        continue;
                    }

                    let mut sub_failures = Vec::new();
                    let mut sub_inferences = inferences.clone();

                    for (lhs_param, rhs_param) in lhs.params.r(s).iter().zip(rhs.params.r(s)) {
                        let TraitParam::Equals(lhs) = *lhs_param else {
                            unreachable!();
                        };

                        let TyOrRe::Ty(lhs) = lhs else {
                            // (regions are ignored)
                            continue;
                        };

                        match rhs_param {
                            TraitParam::Equals(rhs_ty) => {
                                self.check_type_assignability_erase_regions(
                                    lhs,
                                    rhs_ty.unwrap_ty(),
                                    &mut sub_inferences,
                                    &mut sub_failures,
                                );
                            }
                            TraitParam::Unspecified(rhs_clauses) => {
                                self.check_clause_list_assignability_erase_regions(
                                    lhs,
                                    *rhs_clauses,
                                    binder,
                                    &mut sub_inferences,
                                    &mut sub_failures,
                                );
                            }
                        }
                    }

                    if !sub_failures.is_empty() {
                        direct_failures.push(DirectFailure {
                            lhs,
                            cause: sub_failures,
                        });

                        continue;
                    }

                    *inferences = sub_inferences;
                    return;
                }
            }
        }

        failures.push(SatisfiabilityFailure::CannotDirect {
            lhs_instantiated,
            rhs,
            direct_failures,
        });
    }
}

#[derive(Debug, Clone)]
pub enum SatisfiabilityFailure {
    Structural {
        lhs: Ty,
        rhs: Ty,
    },
    CannotSatisfy {
        lhs: Ty,
        rhs: TraitSpec,
        direct_satisfy_failures: Option<Vec<SatisfiabilityFailure>>,
        impl_failures: Vec<ImplFailure>,
    },
    CannotDirect {
        lhs_instantiated: TraitClauseList,
        rhs: TraitSpec,
        direct_failures: Vec<DirectFailure>,
    },
}

#[derive(Debug, Clone)]
pub struct ImplFailure {
    pub impl_: Obj<ImplDef>,
    pub cause: Vec<SatisfiabilityFailure>,
}

#[derive(Debug, Clone)]
pub struct DirectFailure {
    pub lhs: TraitSpec,
    pub cause: Vec<SatisfiabilityFailure>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ImplFreshInfer {
    pub target: Ty,
    pub trait_instance: TyOrReList,
    pub inf_var_clauses: ListOfTraitClauseList,
}

#[derive(Debug, Clone, Default)]
pub struct InferVarInferences {
    disjoint: DisjointSetVec<Option<Ty>>,
}

impl InferVarInferences {
    pub fn next_infer_var(&self) -> InferTyVar {
        InferTyVar(self.disjoint.len() as u32)
    }

    pub fn define_infer_vars(&mut self, count: usize) {
        for _ in 0..count {
            self.disjoint.push(None);
        }
    }

    pub fn assign(&mut self, var: InferTyVar, ty: Ty) {
        let root = self.disjoint.root_of(var.0 as usize);
        let root = &mut self.disjoint[root];

        debug_assert!(root.is_none());
        *root = Some(ty);
    }

    pub fn lookup(&self, var: InferTyVar) -> Option<Ty> {
        self.disjoint[self.disjoint.root_of(var.0 as usize)]
    }

    pub fn union(&mut self, lhs: InferTyVar, rhs: InferTyVar) {
        let lhs_ty = self.lookup(lhs);
        let rhs_ty = self.lookup(rhs);

        debug_assert!(lhs_ty.is_none() || rhs_ty.is_none());

        self.disjoint.join(lhs.0 as usize, rhs.0 as usize);

        let new_root = self.disjoint.root_of(lhs.0 as usize);
        self.disjoint[new_root] = lhs_ty.or(rhs_ty);
    }
}
