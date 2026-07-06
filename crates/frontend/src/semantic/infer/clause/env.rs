use crate::{
    base::{
        arena::{HasInterner as _, HasListInterner as _, Obj},
        syntax::Span,
    },
    semantic::{
        infer::{
            ClauseCx, ClauseImportEnv, GenericSubst, HrtbUniverse, ObligeCause, ObligeCauseStep,
        },
        syntax::{
            AdtInstance, AdtItem, AnyGeneric, FnDef, FnDefOwner, FnInstance, FnInstanceInner,
            FnOwner, GenericBinder, HrtbBinder, HrtbBinderKind, ImplItem, InferTyVarSourceInfo,
            RelationMode, SpannedTraitClauseView, TraitClause, TraitInstance, TraitItem,
            TraitParam, TraitSpec, Ty, TyKind, TyList, TyOrRe, TyOrReList, TypeAliasItem,
            UniversalReVarSourceInfo, UniversalTyVarSourceInfo,
        },
    },
};

// === Universal === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn universal_env(&mut self) -> ClauseCxUniversalEnvBuilder<'_, 'tcx> {
        ClauseCxUniversalEnvBuilder { ccx: self }
    }
}

pub struct ClauseCxUniversalEnvBuilder<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
}

// Machinery
impl ClauseCxUniversalEnvBuilder<'_, '_> {
    pub fn binder_to_init_vars(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        binder_parent_env: &ClauseImportEnv,
        binder: Obj<GenericBinder>,
    ) -> TyOrReList {
        let substs = self.binder_to_uninit_vars(universe, binder);
        self.init_vars_for_binder(cause, universe, binder_parent_env, binder, substs);
        substs
    }

    pub fn binder_to_uninit_vars(
        &mut self,
        universe: &HrtbUniverse,
        binder: Obj<GenericBinder>,
    ) -> TyOrReList {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        let vars =
            binder
                .r(s)
                .defs
                .iter()
                .map(|&generic| match generic {
                    AnyGeneric::Re(generic) => TyOrRe::Re(
                        self.ccx
                            .fresh_re_universal(UniversalReVarSourceInfo::Root(generic)),
                    ),
                    AnyGeneric::Ty(generic) => TyOrRe::Ty(self.ccx.fresh_ty_universal(
                        universe.clone(),
                        UniversalTyVarSourceInfo::Root(generic),
                    )),
                })
                .collect::<Vec<_>>();

        tcx.intern_list(&vars)
    }

    pub fn init_vars_for_binder(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        binder_parent_env: &ClauseImportEnv,
        target_binder: Obj<GenericBinder>,
        target_vars: TyOrReList,
    ) {
        let s = self.ccx.session();

        let binder_env = binder_parent_env
            .clone()
            .with_subst(GenericSubst::new(target_binder, target_vars));

        for (&generic, &subst) in target_binder.r(s).defs.iter().zip(target_vars.r(s)) {
            match (generic, subst) {
                (AnyGeneric::Re(generic), TyOrRe::Re(target)) => {
                    for &clause in generic.r(s).clauses.value.r(s) {
                        let clause = self
                            .ccx
                            .importer()
                            .with_expansion_cause(cause.clone())
                            .import_report_elsewhere(universe, &binder_env, clause);

                        let TraitClause::Outlives(allowed_to_outlive_dir, allowed_to_outlive) =
                            clause
                        else {
                            unreachable!()
                        };

                        self.ccx.permit_universe_re_outlives_general(
                            target,
                            allowed_to_outlive,
                            allowed_to_outlive_dir,
                        );
                    }
                }
                (AnyGeneric::Ty(generic), TyOrRe::Ty(target_ty)) => {
                    let TyKind::UniversalVar(target) = *target_ty.r(s) else {
                        unreachable!()
                    };

                    let clauses = self
                        .ccx
                        .importer()
                        .with_clause_applies_to(target_ty)
                        .import_report_elsewhere(universe, &binder_env, generic.r(s).clauses.value);

                    self.ccx
                        .init_ty_universal_var_direct_clauses(target, clauses);
                }
                _ => unreachable!(),
            }
        }
    }
}

// Specialized
impl ClauseCxUniversalEnvBuilder<'_, '_> {
    pub fn env_for_trait_def(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        def: Obj<TraitItem>,
    ) -> ClauseImportEnv {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        // Create a universal variable representing `Self`
        let self_var = self
            .ccx
            .fresh_ty_universal_var(universe.clone(), UniversalTyVarSourceInfo::TraitSelf);

        let self_ty = tcx.intern(TyKind::UniversalVar(self_var));

        // Create universal variables for each parameter.
        let generic_params = self.binder_to_init_vars(
            cause,
            universe,
            &ClauseImportEnv::new(self_ty, []),
            *def.r(s).generics,
        );

        // Make `Self` implement the trait with these synthesized parameters.
        self.ccx.init_ty_universal_var_direct_clauses(
            self_var,
            tcx.intern_list(&[TraitClause::Trait(HrtbBinder {
                kind: HrtbBinderKind::Imported(tcx.intern_list(&[])),
                inner: TraitSpec {
                    def,
                    params: tcx.intern_list(
                        &generic_params
                            .r(s)
                            .iter()
                            .map(|&arg| TraitParam::Equals(arg))
                            .collect::<Vec<_>>(),
                    ),
                },
            })]),
        );

        ClauseImportEnv::new(
            self_ty,
            [GenericSubst::new(*def.r(s).generics, generic_params)],
        )
    }

    pub fn env_for_adt_def(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        def: Obj<AdtItem>,
    ) -> ClauseImportEnv {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        // Create universal parameters.
        let sig_generic_substs = self.binder_to_uninit_vars(universe, def.r(s).generics);

        // Create the `Self` type.
        let self_ty = tcx.intern(TyKind::Adt(AdtInstance {
            def,
            params: sig_generic_substs,
        }));

        // Initialize the clauses.
        self.init_vars_for_binder(
            cause,
            universe,
            &ClauseImportEnv::new(self_ty, []),
            def.r(s).generics,
            sig_generic_substs,
        );

        ClauseImportEnv::new(
            self_ty,
            [GenericSubst::new(def.r(s).generics, sig_generic_substs)],
        )
    }

    pub fn env_for_impl_block(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        def: Obj<ImplItem>,
    ) -> ClauseImportEnv {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        // Create universal parameters.
        let sig_generic_substs = self.binder_to_uninit_vars(universe, def.r(s).generics);

        // Create the `Self` type.
        let self_ty = self
            .ccx
            .importer()
            .with_expansion_cause(cause.clone())
            .import_report_elsewhere(
                universe,
                &ClauseImportEnv::new(
                    // This type cannot contain `Self` so we give a dummy self type.
                    tcx.intern(TyKind::SigThis),
                    [GenericSubst::new(def.r(s).generics, sig_generic_substs)],
                ),
                def.r(s).target.value,
            );

        // Initialize the clauses.
        self.init_vars_for_binder(
            cause,
            universe,
            &ClauseImportEnv::new(self_ty, []),
            def.r(s).generics,
            sig_generic_substs,
        );

        ClauseImportEnv::new(
            self_ty,
            [GenericSubst::new(def.r(s).generics, sig_generic_substs)],
        )
    }

    pub fn env_for_fn_def(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        def: Obj<FnDef>,
    ) -> ClauseImportEnv {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        // Get parent environment
        let mut env = match *def.r(s).owner {
            FnDefOwner::Item(_item) => ClauseImportEnv::new(tcx.intern(TyKind::SigThis), []),
            FnDefOwner::TraitMethod(def, _idx) => self.env_for_trait_def(cause, universe, def),
            FnDefOwner::ImplMethod(def, _idx) => self.env_for_impl_block(cause, universe, def),
        };

        // Extend with function environment
        let substs = self.binder_to_init_vars(cause, universe, &env, def.r(s).generics);

        env.push_subst(GenericSubst::new(def.r(s).generics, substs));

        env
    }

    pub fn env_for_type_alias_def(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        def: Obj<TypeAliasItem>,
    ) -> ClauseImportEnv {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        let self_ty = tcx.intern(TyKind::SigThis);

        let substs = self.binder_to_init_vars(
            cause,
            universe,
            &ClauseImportEnv::new(self_ty, []),
            def.r(s).generics,
        );

        ClauseImportEnv::new(
            self_ty,
            [GenericSubst {
                binder: def.r(s).generics,
                substs,
            }],
        )
    }
}

// === Existential === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn existential_env(&mut self) -> ClauseCxExistentialEnvBuilder<'_, 'tcx> {
        ClauseCxExistentialEnvBuilder { ccx: self }
    }
}

pub struct ClauseCxExistentialEnvBuilder<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
}

// Machinery
impl<'tcx> ClauseCxExistentialEnvBuilder<'_, 'tcx> {
    pub fn binder_to_constrained_vars(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        binder_parent_env: &ClauseImportEnv,
        binder: Obj<GenericBinder>,
    ) -> TyOrReList {
        let substs = self.binder_to_unconstrained_vars(universe, binder);
        self.init_constraints_for_binder(cause, universe, binder_parent_env, binder, substs);
        substs
    }

    pub fn binder_to_unconstrained_vars(
        &mut self,
        universe: &HrtbUniverse,
        binder: Obj<GenericBinder>,
    ) -> TyOrReList {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        let substs =
            binder
                .r(s)
                .defs
                .iter()
                .map(|&generic| match generic {
                    AnyGeneric::Re(_) => TyOrRe::Re(self.ccx.fresh_re_infer()),
                    AnyGeneric::Ty(_) => TyOrRe::Ty(self.ccx.fresh_ty_infer(
                        universe.clone(),
                        InferTyVarSourceInfo::UniversalElabHelper,
                    )),
                })
                .collect::<Vec<_>>();

        tcx.intern_list(&substs)
    }

    pub fn init_constraints_for_binder(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        binder_parent_env: &ClauseImportEnv,
        target_binder: Obj<GenericBinder>,
        target_vars: TyOrReList,
    ) {
        let s = self.ccx.session();

        let binder_own_env = binder_parent_env
            .clone()
            .with_subst(GenericSubst::new(target_binder, target_vars));

        self.init_constraints_for_binder_raw(
            universe,
            &binder_own_env,
            &target_binder.r(s).defs,
            target_vars.r(s),
            |_ccx, _idx, clause| {
                cause
                    .clone()
                    .child(ObligeCauseStep::ImportEnvMeetsRequirements { clause }.into())
            },
        )
    }

    pub fn init_constraints_for_binder_raw(
        &mut self,
        universe: &HrtbUniverse,
        binder_own_env: &ClauseImportEnv,
        target_binder: &[AnyGeneric],
        target_vars: &[TyOrRe],
        mut gen_cause: impl FnMut(&mut ClauseCx<'tcx>, usize, Span) -> ObligeCause,
    ) {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        for (i, (&generic, &var)) in target_binder.iter().zip(target_vars).enumerate() {
            match (generic, var) {
                (AnyGeneric::Re(generic), TyOrRe::Re(var)) => {
                    for clause in generic.r(s).clauses.iter(tcx) {
                        let clause_span = clause.own_span();

                        let SpannedTraitClauseView::Outlives(must_outlive_dir, must_outlive) =
                            clause.view(tcx)
                        else {
                            unreachable!()
                        };

                        let cause = gen_cause(&mut self.ccx, i, clause_span);

                        let must_outlive = self
                            .ccx
                            .importer()
                            .with_expansion_cause(cause.clone())
                            .import_report_elsewhere(universe, binder_own_env, must_outlive.value);

                        self.ccx.oblige_general_outlives(
                            cause,
                            TyOrRe::Re(var),
                            must_outlive,
                            must_outlive_dir,
                        );
                    }
                }
                (AnyGeneric::Ty(generic), TyOrRe::Ty(var)) => {
                    for clause in generic.r(s).clauses.iter(tcx) {
                        let cause = gen_cause(&mut self.ccx, i, clause.own_span());

                        let clause = self
                            .ccx
                            .importer()
                            .with_expansion_cause(cause.clone())
                            .with_clause_applies_to(var)
                            .import_report_elsewhere(&universe, binder_own_env, clause.value);

                        match clause {
                            TraitClause::Outlives(must_outlive_dir, must_outlive) => {
                                self.ccx.oblige_general_outlives(
                                    cause,
                                    TyOrRe::Ty(var),
                                    must_outlive,
                                    must_outlive_dir,
                                );
                            }
                            TraitClause::Trait(rhs) => {
                                self.ccx
                                    .oblige_ty_meets_trait(cause, universe.clone(), var, rhs);
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}

// Specialized
impl ClauseCxExistentialEnvBuilder<'_, '_> {
    pub fn instantiate_method_fn_owner(
        &mut self,
        cause: &ObligeCause,
        def: Obj<FnDef>,
        self_ty: Ty,
    ) -> FnOwner {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        match *def.r(s).owner {
            FnDefOwner::Item(_) => unreachable!("not a method"),
            FnDefOwner::ImplMethod(block, method_idx) => FnOwner::Inherent {
                self_ty,
                block,
                method_idx,
            },
            FnDefOwner::TraitMethod(trait_item, method_idx) => {
                let params = self.binder_to_constrained_vars(
                    cause,
                    HrtbUniverse::ROOT_REF,
                    &ClauseImportEnv::new(self_ty, []),
                    *trait_item.r(s).generics,
                );

                let params = tcx.intern_list(
                    &params
                        .r(s)
                        .iter()
                        .copied()
                        .map(TraitParam::Equals)
                        .collect::<Vec<_>>(),
                );

                FnOwner::Trait {
                    instance: TraitSpec {
                        def: trait_item,
                        params,
                    },
                    self_ty,
                    method_idx,
                }
            }
        }
    }

    pub fn instantiate_trait_spec(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        self_ty: Ty,
        spec: TraitSpec,
    ) -> TraitInstance {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        let params = spec
            .params
            .r(s)
            .iter()
            .map(|&param| match param {
                TraitParam::Equals(value) => value,
                TraitParam::Unspecified(clauses) => {
                    let ty = self.ccx.fresh_ty_infer(
                        universe.clone(),
                        InferTyVarSourceInfo::TraitAssocPlaceholderHelper,
                    );
                    self.ccx
                        .oblige_ty_meets_clauses(cause, universe, ty, clauses);

                    TyOrRe::Ty(ty)
                }
            })
            .collect::<Vec<_>>();

        let params = tcx.intern_list(&params);

        let instance = TraitInstance {
            def: spec.def,
            params,
        };

        self.ccx.oblige_ty_meets_trait_instantiated(
            cause.clone(),
            universe.clone(),
            self_ty,
            // Force the fresh variables to be properly constrained.
            instance.to_spec(tcx),
        );

        instance
    }

    pub fn env_of_fn_def_for_owner(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        owner: FnOwner,
    ) -> ClauseImportEnv {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        match owner {
            FnOwner::Item(_) => ClauseImportEnv::new(tcx.intern(TyKind::SigThis), Vec::new()),
            FnOwner::Trait {
                instance,
                self_ty,
                method_idx: _,
            } => {
                let instance = self.instantiate_trait_spec(cause, universe, self_ty, instance);

                ClauseImportEnv::new(
                    self_ty,
                    [GenericSubst::new(
                        *instance.def.r(s).generics,
                        instance.params,
                    )],
                )
            }
            FnOwner::Inherent {
                self_ty,
                block,
                method_idx: _,
            } => {
                let block_params = self.binder_to_constrained_vars(
                    cause,
                    universe,
                    &ClauseImportEnv::new(self_ty, Vec::new()),
                    block.r(s).generics,
                );

                let block_env = ClauseImportEnv::new(
                    self_ty,
                    [GenericSubst::new(block.r(s).generics, block_params)],
                );

                let expected_self_ty = self
                    .ccx
                    .importer()
                    .with_expansion_cause(cause.clone())
                    .import_report_elsewhere(&universe, &block_env, block.r(s).target.value);

                self.ccx.oblige_ty_unifies_ty(
                    cause.clone(),
                    self_ty,
                    expected_self_ty,
                    RelationMode::Equate,
                );

                block_env
            }
        }
    }

    pub fn env_of_fn_def_for_instance(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        instance: FnInstance,
    ) -> ClauseImportEnv {
        let s = self.ccx.session();

        let FnInstanceInner { owner, early_args } = *instance.r(s);

        let mut env = self.env_of_fn_def_for_owner(cause, universe, owner);
        let def = owner.def(s);

        env.sig_generic_substs.push(GenericSubst::new(
            def.r(s).generics,
            if let Some(early_args) = early_args {
                early_args
            } else {
                self.binder_to_constrained_vars(cause, universe, &env, def.r(s).generics)
            },
        ));

        env
    }
}

// === Misc Helpers === //

impl ClauseCx<'_> {
    pub fn import_fn_instance_receiver_as_infer(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        env: &ClauseImportEnv,
        def: Obj<FnDef>,
    ) -> Ty {
        let s = self.session();

        debug_assert!(*def.r(s).has_self_param);

        self.importer()
            .with_expansion_cause(cause.clone())
            .import_report_elsewhere(universe, env, def.r(s).args.r(s)[0].ty.value)
    }

    pub fn import_fn_instance_sig(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        env: &ClauseImportEnv,
        def: Obj<FnDef>,
    ) -> (TyList, Ty) {
        let s = self.session();
        let tcx = self.tcx();

        let args = def
            .r(s)
            .args
            .r(s)
            .iter()
            .map(|v| v.ty.value)
            .collect::<Vec<_>>();

        let args = tcx.intern_list(&args);

        let args = self
            .importer()
            .with_expansion_cause(cause.clone())
            .import_report_elsewhere(universe, env, args);

        let ret_ty = self
            .importer()
            .with_expansion_cause(cause.clone())
            .import_report_elsewhere(universe, env, def.r(s).ret_ty.value);

        (args, ret_ty)
    }
}
