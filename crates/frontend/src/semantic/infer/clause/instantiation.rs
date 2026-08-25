use crate::{
    base::arena::{HasInterner as _, HasListInterner as _, Obj},
    semantic::{
        infer::{
            BinderParamWfBinderError, BinderParamWfParamError, BinderParamWfParamErrorKind,
            ClauseCx, ClauseFuel, ClauseImportEnv, CreateWfObligations, GenericSubst, HrtbUniverse,
            ImplBlockSatisfyError, ImplBlockSatisfyErrorCulprit, ImportWfReportElsewhereExt,
            MultiPromiseBuilder, Promise, PromiseValue, TraitSpecResolutionError,
            TraitSpecResolutionErrorCulprit,
        },
        syntax::{
            AdtInstance, AdtItem, AnyGeneric, FnDef, FnDefOwner, FnInstance, FnOwner,
            FnOwnerAdtCtor, FnOwnerInherent, FnOwnerTrait, GenericBinder, HrtbBinder, ImplItem,
            InferTyVarSourceInfo, InstantiatedFnSig, RelationMode, SigTraitClauseKind, TraitClause,
            TraitInstance, TraitItem, TraitParam, TraitSpec, Ty, TyKind, TyOrRe, TyOrReKind,
            TyOrReList, TypeAliasItem, TypeGeneric, UniversalReVarSourceInfo,
            UniversalTyVarSourceInfo,
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

/// Machinery
impl<'tcx> ClauseCxInferInstantiation<'_, 'tcx> {
    pub fn fresh_binder_to_unconstrained_params(
        &mut self,
        universe: &HrtbUniverse,
        binder: Obj<GenericBinder>,
        mut create_info: impl FnMut(
            &mut ClauseCx<'tcx>,
            usize,
            Obj<TypeGeneric>,
        ) -> InferTyVarSourceInfo,
    ) -> TyOrReList {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        tcx.intern_list(
            &binder
                .r(s)
                .defs
                .iter()
                .enumerate()
                .map(|(idx, &def)| match def {
                    AnyGeneric::Re(_) => TyOrRe::Re(self.ccx.fresh_re_infer()),
                    AnyGeneric::Ty(def) => {
                        let info = create_info(self.ccx, idx, def);

                        TyOrRe::Ty(self.ccx.fresh_ty_infer(universe.clone(), info))
                    }
                })
                .collect::<Vec<_>>(),
        )
    }

    pub fn ensure_binder_params_wf(
        &mut self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        binder: Obj<GenericBinder>,
        binder_env: ClauseImportEnv,
        verify_first_n: Option<u32>,
        params: impl IntoIterator<Item = TyOrRe>,
    ) -> Promise<'tcx, BinderParamWfBinderError> {
        let s = self.ccx.session();

        let mut collector = MultiPromiseBuilder::new();

        for (idx, (&generic, var)) in binder
            .r(s)
            .defs
            .iter()
            .zip(params)
            .take(verify_first_n.map_or(usize::MAX, |v| v as usize))
            .enumerate()
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
                                fuel,
                                universe.clone(),
                                binder_env.clone(),
                                // We skip WF for the *condition itself* since generic binders are
                                // WF-checked elsewhere and should not have any inference variables
                                // requiring a re-issuing of the WF obligations.
                                SigImporterWfMode::Skip,
                            )
                            .import_ty_or_re(must_outlive)
                            .report_wf_elsewhere()
                            .map(move |_ccx, error| BinderParamWfParamError {
                                idx: idx as u32,
                                kind: BinderParamWfParamErrorKind::ClauseFuelError(error),
                            })
                            .join(&mut collector);

                        self.ccx
                            .oblige_general_outlives(
                                TyOrRe::Re(var),
                                must_outlive,
                                must_outlive_dir,
                            )
                            .map(move |_ccx, error| BinderParamWfParamError {
                                idx: idx as u32,
                                kind: BinderParamWfParamErrorKind::OutlivesNotMet(error),
                            })
                            .join(&mut collector);
                    }
                }
                (AnyGeneric::Ty(generic), TyOrRe::Ty(var)) => {
                    for &clause in generic.r(s).clauses.elems.r(s) {
                        let clause = self
                            .ccx
                            .importer(
                                fuel,
                                universe.clone(),
                                binder_env.clone(),
                                // See above.
                                SigImporterWfMode::Skip,
                            )
                            .import_trait_clause(clause)
                            .report_wf_elsewhere()
                            .map(move |_ccx, error| BinderParamWfParamError {
                                idx: idx as u32,
                                kind: BinderParamWfParamErrorKind::ClauseFuelError(error),
                            })
                            .join(&mut collector);

                        match clause {
                            TraitClause::Outlives(must_outlive_dir, must_outlive) => {
                                self.ccx
                                    .oblige_general_outlives(
                                        TyOrRe::Ty(var),
                                        must_outlive,
                                        must_outlive_dir,
                                    )
                                    .map(move |_ccx, error| BinderParamWfParamError {
                                        idx: idx as u32,
                                        kind: BinderParamWfParamErrorKind::OutlivesNotMet(error),
                                    })
                                    .join(&mut collector);
                            }
                            TraitClause::Trait(rhs) => {
                                self.ccx
                                    .oblige_ty_meets_trait(fuel, universe.clone(), var, rhs)
                                    .map(move |_ccx, error| BinderParamWfParamError {
                                        idx: idx as u32,
                                        kind: BinderParamWfParamErrorKind::ImplNotMet(error),
                                    })
                                    .join(&mut collector);
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
        }

        collector
            .finish()
            .map(move |_ccx, errors| BinderParamWfBinderError { binder, errors })
    }
}

/// Full resolution
impl<'tcx> ClauseCxInferInstantiation<'_, 'tcx> {
    /// Resolves all the projected types of a `TraitSpec` applying to a specified `self_ty`,
    /// returning a complete `TraitInstance`.
    pub fn resolve_trait_spec(
        &mut self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        self_ty: Ty,
        spec: TraitSpec,
    ) -> PromiseValue<'tcx, TraitInstance, TraitSpecResolutionError> {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        let mut collector = MultiPromiseBuilder::new();

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
                        .oblige_ty_meets_clauses(fuel, universe, projection, clauses)
                        .map(
                            move |_ccx, error| TraitSpecResolutionErrorCulprit::AssocParaNotMet {
                                idx: idx as u32,
                                error,
                            },
                        )
                        .join(&mut collector);

                    TyOrRe::Ty(projection)
                }
            })
            .collect::<Vec<_>>();

        let instance = TraitInstance {
            def: spec.def,
            params: tcx.intern_list(&params),
        };

        self.ccx
            .oblige_ty_meets_trait_instantiated(
                fuel,
                universe.clone(),
                self_ty,
                // Force the fresh variables to be properly constrained.
                instance.to_spec(tcx),
            )
            .map(move |_ccx, error| TraitSpecResolutionErrorCulprit::ImplRejected(error))
            .join(&mut collector);

        let promise = collector
            .finish()
            .map(move |_ccx, culprits| TraitSpecResolutionError {
                self_ty,
                spec,
                culprits,
            });

        promise.and_value(instance)
    }

    pub fn resolve_inherent_impl_block_env(
        &mut self,
        universe: &HrtbUniverse,
        block: Obj<ImplItem>,
        self_ty: Ty,
    ) -> InstantiatedImplBlock {
        let instantiation = self.fresh_impl_block(cause, universe, block);

        debug_assert!(instantiation.target_trait.is_none());

        self.ccx.oblige_ty_unifies_ty(
            cause.clone(),
            instantiation.target_ty,
            self_ty,
            RelationMode::Equate,
        );

        instantiation
    }

    pub fn resolve_fn_instance_sig(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        fn_instance: FnInstance,
    ) -> InstantiatedFnSig {
        let tcx = self.ccx.tcx();
        let s = self.ccx.session();

        match fn_instance.r(s).owner {
            FnOwner::Item(def) => {
                let def = *def.r(s).def;

                let fn_binder = def.r(s).generics;
                let early_args = self.fresh_early_args(
                    cause,
                    universe,
                    fn_instance,
                    ClauseImportEnv::new(None, []),
                    fn_binder,
                );

                self.resolve_fn_def_sig(
                    cause,
                    universe,
                    def,
                    ClauseImportEnv::new(None, [GenericSubst::new(fn_binder, early_args)]),
                )
            }
            FnOwner::Trait(FnOwnerTrait {
                instance,
                self_ty,
                method_idx,
            }) => {
                let fn_def = instance.def.r(s).methods[method_idx as usize];
                let fn_binder = fn_def.r(s).generics;

                let instance_binder = *instance.def.r(s).generics;
                let instance = self.resolve_trait_spec(cause, universe, self_ty, instance);

                let early_args = self.fresh_early_args(
                    cause,
                    universe,
                    fn_instance,
                    ClauseImportEnv::new(
                        Some(self_ty),
                        [GenericSubst::new(instance_binder, instance.params)],
                    ),
                    fn_binder,
                );

                self.resolve_fn_def_sig(
                    cause,
                    universe,
                    fn_def,
                    ClauseImportEnv::new(
                        Some(self_ty),
                        [
                            GenericSubst::new(instance_binder, instance.params),
                            GenericSubst::new(fn_binder, early_args),
                        ],
                    ),
                )
            }
            FnOwner::Inherent(FnOwnerInherent {
                self_ty,
                block,
                method_idx,
            }) => {
                let fn_def = block.r(s).methods[method_idx as usize].unwrap();
                let fn_binder = fn_def.r(s).generics;

                let parent_env = self
                    .resolve_inherent_impl_block_env(cause, universe, block, self_ty)
                    .env;

                let early_args = self.fresh_early_args(
                    cause,
                    universe,
                    fn_instance,
                    parent_env.clone(),
                    fn_binder,
                );

                let full_env =
                    parent_env.with_subst(GenericSubst::new(fn_def.r(s).generics, early_args));

                self.resolve_fn_def_sig(cause, universe, fn_def, full_env)
            }
            FnOwner::AdtCtor(FnOwnerAdtCtor { ctor }) => {
                let item = ctor.r(s).owner.item(s);
                let early_args = self.fresh_early_args(
                    cause,
                    universe,
                    fn_instance,
                    ClauseImportEnv::new(None, []),
                    item.r(s).generics,
                );

                let self_ty = tcx.intern(TyKind::Adt(AdtInstance {
                    def: item,
                    params: early_args,
                }));

                let env = ClauseImportEnv::new(
                    Some(self_ty),
                    [GenericSubst::new(item.r(s).generics, early_args)],
                );

                let args = tcx.intern_list(
                    &ctor
                        .r(s)
                        .fields
                        .iter()
                        .map(|field| {
                            self.ccx
                                .importer(
                                    cause.clone(),
                                    universe.clone(),
                                    env.clone(),
                                    SigImporterWfMode::DelayBug,
                                )
                                .import_ty(*field.ty)
                        })
                        .collect::<Vec<_>>(),
                );

                InstantiatedFnSig {
                    args,
                    ret_ty: self_ty,
                }
            }
        }
    }

    fn fresh_early_args(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        fn_instance: FnInstance,
        parent_env: ClauseImportEnv,
        binder: Obj<GenericBinder>,
    ) -> TyOrReList {
        let s = self.ccx.session();

        if let Some(provided) = fn_instance.r(s).early_args {
            return provided;
        }

        let early_args =
            self.fresh_binder_to_unconstrained_params(universe, binder, |_ccx, idx, _generic| {
                InferTyVarSourceInfo::LateBoundFnGeneric {
                    instance: fn_instance,
                    idx: idx as u32,
                }
            });

        let spanned_early_args =
            early_args
                .r(s)
                .iter()
                .zip(&binder.r(s).defs)
                .map(|(&para, generic)| {
                    let cause = cause.clone().child(ObligeCauseFrame::Step(
                        ObligeCauseStep::ImportEnvMeetsRequirements {
                            clause: generic.span(s),
                        },
                    ));

                    (cause, para)
                });

        self.ensure_binder_params_wf(universe, binder, parent_env, None, spanned_early_args);

        early_args
    }

    pub fn resolve_fn_def_sig(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        def: Obj<FnDef>,
        env: ClauseImportEnv,
    ) -> InstantiatedFnSig {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        InstantiatedFnSig {
            args: tcx.intern_list(
                &def.r(s)
                    .args
                    .r(s)
                    .iter()
                    .map(|arg| {
                        self.ccx
                            .importer(
                                cause.clone(),
                                universe.clone(),
                                env.clone(),
                                SigImporterWfMode::DelayBug,
                            )
                            .import_ty(arg.ty)
                    })
                    .collect::<Vec<_>>(),
            ),
            ret_ty: self
                .ccx
                .importer(
                    cause.clone(),
                    universe.clone(),
                    env.clone(),
                    SigImporterWfMode::DelayBug,
                )
                .import_ty(*def.r(s).ret_ty),
        }
    }
}

#[derive(Debug, Clone)]
pub struct InstantiatedImplBlock {
    pub env: ClauseImportEnv,
    pub params: TyOrReList,
    pub target_ty: Ty,
    pub target_trait: Option<TraitInstance>,
}

#[derive(Debug, Clone)]
pub struct SignatureMismatchError;

/// Instantiation.
impl<'tcx> ClauseCxInferInstantiation<'_, 'tcx> {
    fn fresh_trait_item_to_unconstrained_trait_spec(
        &mut self,
        universe: &HrtbUniverse,
        item: Obj<TraitItem>,
    ) -> TraitSpec {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        let params = tcx.intern_list(
            &item
                .r(s)
                .generics
                .r(s)
                .defs
                .iter()
                .enumerate()
                .map(|(idx, def)| {
                    if idx >= *item.r(s).regular_generic_count as usize {
                        debug_assert_eq!(def.kind(), TyOrReKind::Ty);

                        return TraitParam::Unspecified(tcx.intern_list(&[]));
                    }

                    match def.kind() {
                        TyOrReKind::Re => TraitParam::Equals(TyOrRe::Re(self.ccx.fresh_re_infer())),
                        TyOrReKind::Ty => TraitParam::Equals(TyOrRe::Ty(self.ccx.fresh_ty_infer(
                            universe.clone(),
                            InferTyVarSourceInfo::TraitParam {
                                trait_: item,
                                idx: idx as u32,
                            },
                        ))),
                    }
                })
                .collect::<Vec<_>>(),
        );

        TraitSpec { def: item, params }
    }

    pub fn fresh_type_relative_fn_def_to_fn_owner(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        self_ty: Ty,
        def: Obj<FnDef>,
    ) -> FnOwner {
        let s = self.ccx.session();

        match *def.r(s).owner {
            FnDefOwner::Item(_) => unreachable!(),
            FnDefOwner::TraitMethod(item, method_idx) => {
                let instance = self.fresh_trait_item_to_unconstrained_trait_spec(universe, item);

                self.ccx.oblige_ty_meets_trait_instantiated(
                    cause.clone(),
                    universe.clone(),
                    self_ty,
                    instance,
                );

                FnOwner::Trait(FnOwnerTrait {
                    instance,
                    self_ty,
                    method_idx,
                })
            }
            FnDefOwner::ImplMethod(block, method_idx) => FnOwner::Inherent(FnOwnerInherent {
                self_ty,
                block,
                method_idx,
            }),
        }
    }

    pub fn fresh_impl_block(
        &mut self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        block: Obj<ImplItem>,
    ) -> PromiseValue<'tcx, InstantiatedImplBlock, ImplBlockSatisfyError> {
        let s = self.ccx.session();

        let mut collector = MultiPromiseBuilder::new();

        // Instantiate fresh variables for each `impl` block generic.
        let params = self.fresh_binder_to_unconstrained_params(
            universe,
            block.r(s).generics,
            |_ccx, idx, _def| InferTyVarSourceInfo::ImplBlockParam {
                block,
                idx: idx as u32,
            },
        );

        // Import the target type and trait.
        let mut env = ClauseImportEnv::new(None, [GenericSubst::new(block.r(s).generics, params)]);

        let target_ty = self
            .ccx
            .importer(
                fuel,
                universe.clone(),
                env.clone(),
                CreateWfObligations::Yes,
            )
            .import_ty(*block.r(s).target)
            .report_wf_elsewhere()
            .map(move |_ccx, error| ImplBlockSatisfyErrorCulprit::SelfTyFuelError(error))
            .join(&mut collector);

        env.self_ty = Some(target_ty);

        let target_trait = block.r(s).trait_.map(|trait_| {
            self.ccx
                .importer(
                    fuel,
                    universe.clone(),
                    env.clone(),
                    CreateWfObligations::Yes,
                )
                .import_trait_instance(target_ty, trait_)
                .report_wf_elsewhere()
                .map(move |_ccx, error| ImplBlockSatisfyErrorCulprit::TargetTraitFuelError(error))
                .join(&mut collector)
        });

        self.ensure_binder_params_wf(
            fuel,
            universe,
            block.r(s).generics,
            env.clone(),
            None,
            params.r(s).iter().copied(),
        )
        .map(move |_ccx, error| ImplBlockSatisfyErrorCulprit::GenericsUnsatisfied(error))
        .join(&mut collector);

        let promise = collector
            .finish()
            .map(move |_ccx, culprits| ImplBlockSatisfyError { block, culprits });

        promise.and_value(InstantiatedImplBlock {
            env,
            params,
            target_ty,
            target_trait,
        })
    }
}
