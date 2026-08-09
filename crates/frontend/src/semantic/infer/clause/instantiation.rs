use crate::{
    base::arena::{HasInterner as _, HasListInterner as _, Obj},
    semantic::{
        infer::{
            ClauseCx, ClauseImportEnv, GenericSubst, HrtbUniverse, ObligeCause, ObligeCauseFrame,
            ObligeCauseStep, SigImporterWfMode,
        },
        syntax::{
            AdtInstance, AdtItem, AnyGeneric, FnDef, FnDefOwner, GenericBinder, HrtbBinder,
            ImplItem, InferTyVarSourceInfo, SigTraitClauseKind, TraitClause, TraitInstance,
            TraitItem, TraitParam, TraitSpec, Ty, TyKind, TyOrRe, TyOrReList, TypeAliasItem,
            UniversalReVarSourceInfo, UniversalTyVarSourceInfo,
        },
    },
};

// === Universal === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn instantiate_universal(&mut self) -> ClauseCxUniversalInstantiation<'_, 'tcx> {
        ClauseCxUniversalInstantiation { ccx: self }
    }
}

/// Utilities for instantiating various type system objects universally.
pub struct ClauseCxUniversalInstantiation<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
}

/// Machinery
impl ClauseCxUniversalInstantiation<'_, '_> {
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
                    for &clause in generic.r(s).clauses.elems.r(s) {
                        let clause = self
                            .ccx
                            .importer(
                                cause.clone(),
                                universe.clone(),
                                binder_env.clone(),
                                SigImporterWfMode::Skip,
                            )
                            .import_trait_clause(clause);

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
                        .importer(
                            cause.clone(),
                            universe.clone(),
                            binder_env.clone(),
                            SigImporterWfMode::Skip,
                        )
                        .import_trait_clause_list(*generic.r(s).clauses);

                    self.ccx
                        .init_ty_universal_var_direct_clauses(target, clauses);
                }
                _ => unreachable!(),
            }
        }
    }
}

/// Specialized
impl ClauseCxUniversalInstantiation<'_, '_> {
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
            &ClauseImportEnv::new(Some(self_ty), []),
            *def.r(s).generics,
        );

        // Make `Self` implement the trait with these synthesized parameters.
        self.ccx.init_ty_universal_var_direct_clauses(
            self_var,
            tcx.intern_list(&[TraitClause::Trait(HrtbBinder {
                defs: tcx.intern_list(&[]),
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
            Some(self_ty),
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
            &ClauseImportEnv::new(Some(self_ty), []),
            def.r(s).generics,
            sig_generic_substs,
        );

        ClauseImportEnv::new(
            Some(self_ty),
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

        // Create universal parameters.
        let sig_generic_substs = self.binder_to_uninit_vars(universe, def.r(s).generics);

        // Create the `Self` type.
        let self_ty = self
            .ccx
            .importer(
                cause.clone(),
                universe.clone(),
                ClauseImportEnv::new(
                    None,
                    [GenericSubst::new(def.r(s).generics, sig_generic_substs)],
                ),
                SigImporterWfMode::DelayBug,
            )
            .import_ty(*def.r(s).target);

        // Initialize the clauses.
        self.init_vars_for_binder(
            cause,
            universe,
            &ClauseImportEnv::new(Some(self_ty), []),
            def.r(s).generics,
            sig_generic_substs,
        );

        ClauseImportEnv::new(
            Some(self_ty),
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

        // Get parent environment
        let mut env = match *def.r(s).owner {
            FnDefOwner::Item(_item) => ClauseImportEnv::new(None, []),
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

        let substs = self.binder_to_init_vars(
            cause,
            universe,
            &ClauseImportEnv::new(None, []),
            def.r(s).generics,
        );

        ClauseImportEnv::new(None, [GenericSubst::new(def.r(s).generics, substs)])
    }
}

// === Inference === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn instantiate_infer(&mut self) -> ClauseCxInferInstantiation<'_, 'tcx> {
        ClauseCxInferInstantiation { ccx: self }
    }
}

/// Utilities for instantiating various type system objects with placeholder inference variables.
pub struct ClauseCxInferInstantiation<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
}

impl ClauseCxInferInstantiation<'_, '_> {
    pub fn ensure_binder_params_wf(
        &mut self,
        universe: &HrtbUniverse,
        binder: Obj<GenericBinder>,
        binder_env: ClauseImportEnv,
        verify_first_n: Option<u32>,
        params: impl IntoIterator<Item = (ObligeCause, TyOrRe)>,
    ) {
        let s = self.ccx.session();

        for (&generic, (var_cause, var)) in binder
            .r(s)
            .defs
            .iter()
            .zip(params)
            .take(verify_first_n.map_or(usize::MAX, |v| v as usize))
        {
            match (generic, var) {
                (AnyGeneric::Re(generic), TyOrRe::Re(var)) => {
                    for &clause in generic.r(s).clauses.elems.r(s) {
                        let SigTraitClauseKind::Outlives(must_outlive_dir, must_outlive) =
                            clause.kind
                        else {
                            unreachable!()
                        };

                        let must_outlive = self
                            .ccx
                            .importer(
                                var_cause.clone(),
                                universe.clone(),
                                binder_env.clone(),
                                // We skip WF for the *condition itself* since generic binders are
                                // WF-checked elsewhere and should not have any inference variables
                                // requiring a re-issuing of the WF obligations.
                                SigImporterWfMode::Skip,
                            )
                            .import_ty_or_re(must_outlive);

                        self.ccx.oblige_general_outlives(
                            var_cause.clone(),
                            TyOrRe::Re(var),
                            must_outlive,
                            must_outlive_dir,
                        );
                    }
                }
                (AnyGeneric::Ty(generic), TyOrRe::Ty(var)) => {
                    for &clause in generic.r(s).clauses.elems.r(s) {
                        let clause = self
                            .ccx
                            .importer(
                                var_cause.clone(),
                                universe.clone(),
                                binder_env.clone(),
                                // See above.
                                SigImporterWfMode::Skip,
                            )
                            .import_trait_clause(clause);

                        match clause {
                            TraitClause::Outlives(must_outlive_dir, must_outlive) => {
                                self.ccx.oblige_general_outlives(
                                    var_cause.clone(),
                                    TyOrRe::Ty(var),
                                    must_outlive,
                                    must_outlive_dir,
                                );
                            }
                            TraitClause::Trait(rhs) => {
                                self.ccx.oblige_ty_meets_trait(
                                    var_cause.clone(),
                                    universe.clone(),
                                    var,
                                    rhs,
                                );
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    /// Resolves all the projected types of a `TraitSpec` applying to a specified `self_ty`,
    /// returning a complete `TraitInstance`.
    pub fn resolve_trait_spec(
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
            .enumerate()
            .map(|(idx, &param)| match param {
                TraitParam::Equals(value) => value,
                TraitParam::Unspecified(clauses) => {
                    let projection = self.ccx.fresh_ty_infer(
                        universe.clone(),
                        InferTyVarSourceInfo::Projection {
                            self_ty,
                            spec,
                            idx: idx as u32,
                        },
                    );

                    self.ccx
                        .oblige_ty_meets_clauses(cause, universe, projection, clauses);

                    TyOrRe::Ty(projection)
                }
            })
            .collect::<Vec<_>>();

        let instance = TraitInstance {
            def: spec.def,
            params: tcx.intern_list(&params),
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
}

#[derive(Debug, Clone)]
pub struct InstantiatedImplBlock {
    pub env: ClauseImportEnv,
    pub params: TyOrReList,
    pub target_ty: Ty,
    pub target_trait: TraitInstance,
}

impl ClauseCxInferInstantiation<'_, '_> {
    pub fn fresh_impl_block(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        block: Obj<ImplItem>,
    ) -> InstantiatedImplBlock {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        // Instantiate fresh variables for each `impl` block generic.
        let params = tcx.intern_list(
            &block
                .r(s)
                .generics
                .r(s)
                .defs
                .iter()
                .enumerate()
                .map(|(idx, def)| match def {
                    AnyGeneric::Re(_) => TyOrRe::Re(self.ccx.fresh_re_infer()),
                    AnyGeneric::Ty(_) => TyOrRe::Ty(self.ccx.fresh_ty_infer(
                        universe.clone(),
                        InferTyVarSourceInfo::ImplBlockParam {
                            block,
                            idx: idx as u32,
                        },
                    )),
                })
                .collect::<Vec<_>>(),
        );

        // Import the target type and trait.
        let mut env = ClauseImportEnv::new(None, [GenericSubst::new(block.r(s).generics, params)]);

        let target_ty = self
            .ccx
            .importer(
                cause.clone(),
                universe.clone(),
                env.clone(),
                SigImporterWfMode::DelayBug,
            )
            .import_ty(*block.r(s).target);

        env.self_ty = Some(target_ty);

        let target_trait = self
            .ccx
            .importer(
                cause.clone(),
                universe.clone(),
                env.clone(),
                SigImporterWfMode::DelayBug,
            )
            .import_trait_instance(target_ty, block.r(s).trait_.unwrap());

        let spanned_params =
            params
                .r(s)
                .iter()
                .zip(&block.r(s).generics.r(s).defs)
                .map(|(&para, generic)| {
                    let cause = cause.clone().child(ObligeCauseFrame::Step(
                        ObligeCauseStep::ImportEnvMeetsRequirements {
                            clause: generic.span(s),
                        },
                    ));

                    (cause, para)
                });

        self.ensure_binder_params_wf(
            universe,
            block.r(s).generics,
            env.clone(),
            None,
            spanned_params,
        );

        InstantiatedImplBlock {
            env,
            params,
            target_ty,
            target_trait,
        }
    }
}
