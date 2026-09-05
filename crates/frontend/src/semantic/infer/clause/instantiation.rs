use crate::{
    base::arena::{HasInterner as _, HasListInterner as _, Obj},
    semantic::{
        infer::{
            BinderParamWfBinderError, BinderParamWfParamError, BinderParamWfParamErrorKind,
            ClauseCx, ClauseFuel, ClauseImportEnv, FnInstanceResolutionError,
            FnInstanceResolutionErrorKind, GenericSubst, HrtbUniverse, ImplBlockSatisfyError,
            ImplBlockSatisfyErrorCulprit, ImportError, ImportWfMode, InherentImplBlockSatisfyError,
            MultiPromiseBuilder, MultiPromiseValue, Promise, PromiseValue,
            TraitSpecResolutionError, TraitSpecResolutionErrorCulprit,
            TypeRelativeFnDefToOwnerError,
        },
        syntax::{
            AdtInstance, AdtItem, AnyGeneric, FnDef, FnDefOwner, FnInstance, FnOwner,
            FnOwnerAdtCtor, FnOwnerInherent, FnOwnerTrait, GenericBinder, HrtbBinder, ImplItem,
            InferTyVarSourceInfo, InstantiatedFnSig, RelationMode, SigTraitClauseKind, TraitClause,
            TraitInstance, TraitItem, TraitParam, TraitSpec, Ty, TyKind, TyOrRe, TyOrReKind,
            TyOrReList, TypeAliasItem, TypeGeneric, UniversalReVarSourceInfo, UniversalTy,
            UniversalTyVarSourceInfo,
        },
    },
    typed_joiner,
};

// === Universal === //

/// Machinery
impl<'tcx> ClauseCx<'tcx> {
    fn universal_binder_to_init_vars(
        &mut self,
        binder_parent_env: &ClauseImportEnv,
        binder: Obj<GenericBinder>,
    ) -> TyOrReList {
        let substs = self.universal_binder_to_uninit_vars(binder);
        self.universal_init_vars_for_binder(binder_parent_env, binder, substs);
        substs
    }

    fn universal_binder_to_uninit_vars(&mut self, binder: Obj<GenericBinder>) -> TyOrReList {
        let s = self.session();
        let tcx = self.tcx();

        let vars = binder
            .r(s)
            .defs
            .iter()
            .map(|&generic| match generic {
                AnyGeneric::Re(generic) => {
                    TyOrRe::Re(self.fresh_re_universal(UniversalReVarSourceInfo::Root(generic)))
                }
                AnyGeneric::Ty(generic) => TyOrRe::Ty(self.fresh_ty_universal_root(
                    HrtbUniverse::ROOT,
                    UniversalTyVarSourceInfo::Root(generic),
                )),
            })
            .collect::<Vec<_>>();

        tcx.intern_list(&vars)
    }

    fn universal_init_vars_for_binder(
        &mut self,
        binder_parent_env: &ClauseImportEnv,
        target_binder: Obj<GenericBinder>,
        target_vars: TyOrReList,
    ) {
        let s = self.session();

        let binder_env = binder_parent_env
            .clone()
            .with_subst(GenericSubst::new(target_binder, target_vars));

        for (&generic, &subst) in target_binder.r(s).defs.iter().zip(target_vars.r(s)) {
            match (generic, subst) {
                (AnyGeneric::Re(generic), TyOrRe::Re(target)) => {
                    for &clause in generic.r(s).clauses.elems.r(s) {
                        let clause = self.import_elsewhere(&binder_env, clause);

                        let TraitClause::Outlives(allowed_to_outlive_dir, allowed_to_outlive) =
                            clause
                        else {
                            unreachable!()
                        };

                        self.permit_universe_re_outlives_general(
                            target,
                            allowed_to_outlive,
                            allowed_to_outlive_dir,
                        );
                    }
                }
                (AnyGeneric::Ty(generic), TyOrRe::Ty(target_ty)) => {
                    let TyKind::Universal(target) = *target_ty.r(s) else {
                        unreachable!()
                    };

                    let clauses = self.import_elsewhere(&binder_env, *generic.r(s).clauses);

                    self.init_ty_universal_direct_clauses(target, clauses);
                }
                _ => unreachable!(),
            }
        }
    }
}

/// Specialized
impl<'tcx> ClauseCx<'tcx> {
    pub fn universal_env_for_trait_def(&mut self, def: Obj<TraitItem>) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        // Create a universal variable representing `Self`
        let self_var =
            UniversalTy::Root(self.fresh_ty_universal_root_idx(
                HrtbUniverse::ROOT,
                UniversalTyVarSourceInfo::TraitSelf,
            ));

        let self_ty = tcx.intern(TyKind::Universal(self_var));

        // Create universal variables for each parameter.
        let generic_params = self.universal_binder_to_init_vars(
            &ClauseImportEnv::new(Some(self_ty), []),
            *def.r(s).generics,
        );

        // Make `Self` implement the trait with these synthesized parameters.
        self.init_ty_universal_direct_clauses(
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

    pub fn universal_env_for_adt_def(&mut self, def: Obj<AdtItem>) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        // Create universal parameters.
        let sig_generic_substs = self.universal_binder_to_uninit_vars(def.r(s).generics);

        // Create the `Self` type.
        let self_ty = tcx.intern(TyKind::Adt(AdtInstance {
            def,
            params: sig_generic_substs,
        }));

        // Initialize the clauses.
        self.universal_init_vars_for_binder(
            &ClauseImportEnv::new(Some(self_ty), []),
            def.r(s).generics,
            sig_generic_substs,
        );

        ClauseImportEnv::new(
            Some(self_ty),
            [GenericSubst::new(def.r(s).generics, sig_generic_substs)],
        )
    }

    pub fn universal_env_for_impl_block(&mut self, def: Obj<ImplItem>) -> ClauseImportEnv {
        let s = self.session();

        // Create universal parameters.
        let sig_generic_substs = self.universal_binder_to_uninit_vars(def.r(s).generics);

        // Create the `Self` type.
        let self_ty = self.import_elsewhere(
            &ClauseImportEnv::new(
                None,
                [GenericSubst::new(def.r(s).generics, sig_generic_substs)],
            ),
            *def.r(s).target,
        );

        // Initialize the clauses.
        self.universal_init_vars_for_binder(
            &ClauseImportEnv::new(Some(self_ty), []),
            def.r(s).generics,
            sig_generic_substs,
        );

        ClauseImportEnv::new(
            Some(self_ty),
            [GenericSubst::new(def.r(s).generics, sig_generic_substs)],
        )
    }

    pub fn universal_env_for_fn_def(&mut self, def: Obj<FnDef>) -> ClauseImportEnv {
        let s = self.session();

        // Get parent environment
        let env = match *def.r(s).owner {
            FnDefOwner::Item(_item) => ClauseImportEnv::new(None, []),
            FnDefOwner::TraitMethod(def, _idx) => self.universal_env_for_trait_def(def),
            FnDefOwner::ImplMethod(def, _idx) => self.universal_env_for_impl_block(def),
        };

        // Extend with function environment
        let substs = self.universal_binder_to_init_vars(&env, def.r(s).generics);

        env.with_subst(GenericSubst::new(def.r(s).generics, substs))
    }

    pub fn universal_env_for_type_alias_def(&mut self, def: Obj<TypeAliasItem>) -> ClauseImportEnv {
        let s = self.session();

        let substs =
            self.universal_binder_to_init_vars(&ClauseImportEnv::new(None, []), def.r(s).generics);

        ClauseImportEnv::new(None, [GenericSubst::new(def.r(s).generics, substs)])
    }
}

// === Inference === //

/// Machinery
impl<'tcx> ClauseCx<'tcx> {
    pub fn fresh_binder_to_unconstrained_infer_params(
        &mut self,
        universe: &HrtbUniverse,
        binder: Obj<GenericBinder>,
        mut create_info: impl FnMut(
            &mut ClauseCx<'tcx>,
            usize,
            Obj<TypeGeneric>,
        ) -> InferTyVarSourceInfo,
    ) -> TyOrReList {
        let s = self.session();
        let tcx = self.tcx();

        tcx.intern_list(
            &binder
                .r(s)
                .defs
                .iter()
                .enumerate()
                .map(|(idx, &def)| match def {
                    AnyGeneric::Re(_) => TyOrRe::Re(self.fresh_re_infer()),
                    AnyGeneric::Ty(def) => {
                        let info = create_info(self, idx, def);

                        TyOrRe::Ty(self.fresh_ty_infer(universe.clone(), info))
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
        params: TyOrReList,
    ) -> Promise<'tcx, BinderParamWfBinderError> {
        let s = self.session();

        let mut collector = MultiPromiseBuilder::new();

        for (idx, (&generic, &var)) in binder
            .r(s)
            .defs
            .iter()
            .zip(params.r(s))
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
                            .importer(
                                fuel,
                                universe.clone(),
                                binder_env.clone(),
                                ImportWfMode::ReportElsewhere,
                            )
                            .import_ty_or_re(must_outlive)
                            .map(move |_ccx, error| BinderParamWfParamError {
                                idx: idx as u32,
                                kind: BinderParamWfParamErrorKind::ClauseCannotImport(error),
                            })
                            .join(&mut collector);

                        self.oblige_general_outlives(
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
                            .importer(
                                fuel,
                                universe.clone(),
                                binder_env.clone(),
                                ImportWfMode::ReportElsewhere,
                            )
                            .import_trait_clause(clause)
                            .map(move |_ccx, error| BinderParamWfParamError {
                                idx: idx as u32,
                                kind: BinderParamWfParamErrorKind::ClauseCannotImport(error),
                            })
                            .join(&mut collector);

                        match clause {
                            TraitClause::Outlives(must_outlive_dir, must_outlive) => {
                                self.oblige_general_outlives(
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
                                self.oblige_ty_meets_trait(fuel, universe.clone(), var, rhs)
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
            .map(move |_ccx, errors| BinderParamWfBinderError {
                binder,
                params,
                errors,
            })
    }
}

/// Full resolution
impl<'tcx> ClauseCx<'tcx> {
    /// Resolves all the projected types of a `TraitSpec` applying to a specified `self_ty`,
    /// returning a complete `TraitInstance`.
    pub fn resolve_trait_spec(
        &mut self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        self_ty: Ty,
        spec: TraitSpec,
    ) -> PromiseValue<'tcx, TraitInstance, TraitSpecResolutionError> {
        let s = self.session();
        let tcx = self.tcx();

        let mut collector = MultiPromiseBuilder::new();

        let params = spec
            .params
            .r(s)
            .iter()
            .enumerate()
            .map(|(idx, &param)| match param {
                TraitParam::Equals(value) => value,
                TraitParam::Unspecified(clauses) => {
                    let projection = self.fresh_ty_infer(
                        universe.clone(),
                        InferTyVarSourceInfo::Projection {
                            self_ty,
                            spec,
                            idx: idx as u32,
                        },
                    );

                    self.oblige_ty_meets_clauses(fuel, universe, projection, clauses)
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

        self.oblige_ty_meets_trait_instantiated(
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
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        block: Obj<ImplItem>,
        self_ty: Ty,
    ) -> PromiseValue<'tcx, InstantiatedImplBlock, InherentImplBlockSatisfyError> {
        let PromiseValue {
            value: instantiation,
            promise: block_clauses_promise,
        } = self.fresh_impl_block(fuel, universe, block);

        debug_assert!(instantiation.target_trait.is_none());

        let self_ty_unify_promise =
            self.oblige_ty_unifies_ty(instantiation.target_ty, self_ty, RelationMode::Equate);

        let promise = typed_joiner! {
            let block_clauses = block_clauses_promise;
            let self_ty_unify = self_ty_unify_promise;
            |ccx| InherentImplBlockSatisfyError {
                block_clauses: block_clauses.map(Box::new),
                self_ty_unify: self_ty_unify.map(Box::new),
            }
        };

        promise.and_value(instantiation)
    }

    pub fn resolve_fn_instance_sig(
        &mut self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        fn_instance: FnInstance,
    ) -> PromiseValue<'tcx, InstantiatedFnSig, FnInstanceResolutionError> {
        let tcx = self.tcx();
        let s = self.session();

        match fn_instance.r(s).owner {
            FnOwner::Item(def) => {
                let def = *def.r(s).def;

                let fn_binder = def.r(s).generics;
                let PromiseValue {
                    value: early_args,
                    promise: early_args_err,
                } = self.obtain_fn_instance_early_args(
                    fuel,
                    universe,
                    fn_instance,
                    ClauseImportEnv::new(None, []),
                    fn_binder,
                );

                let PromiseValue {
                    value: sig,
                    promise: sig_import_err,
                } = self.resolve_fn_def_sig(
                    fuel,
                    universe,
                    def,
                    ClauseImportEnv::new(None, [GenericSubst::new(fn_binder, early_args)]),
                );

                let promise = typed_joiner! {
                    let early_args_err = early_args_err;
                    let sig_import_err = sig_import_err;

                    |ccx| FnInstanceResolutionError {
                        instance: fn_instance,
                        kind: FnInstanceResolutionErrorKind::Item {
                            early_args_err: early_args_err.map(Box::new),
                            sig_import_err: sig_import_err,
                        }
                    }
                };

                promise.and_value(sig)
            }
            FnOwner::Trait(FnOwnerTrait {
                instance,
                self_ty,
                method_idx,
            }) => {
                let fn_def = instance.def.r(s).methods[method_idx as usize];
                let fn_binder = fn_def.r(s).generics;

                let instance_binder = *instance.def.r(s).generics;
                let PromiseValue {
                    value: instance,
                    promise: resolve_instance_err,
                } = self.resolve_trait_spec(fuel, universe, self_ty, instance);

                let PromiseValue {
                    value: early_args,
                    promise: early_args_err,
                } = self.obtain_fn_instance_early_args(
                    fuel,
                    universe,
                    fn_instance,
                    ClauseImportEnv::new(
                        Some(self_ty),
                        [GenericSubst::new(instance_binder, instance.params)],
                    ),
                    fn_binder,
                );

                let PromiseValue {
                    value: sig,
                    promise: sig_import_err,
                } = self.resolve_fn_def_sig(
                    fuel,
                    universe,
                    fn_def,
                    ClauseImportEnv::new(
                        Some(self_ty),
                        [
                            GenericSubst::new(instance_binder, instance.params),
                            GenericSubst::new(fn_binder, early_args),
                        ],
                    ),
                );

                let promise = typed_joiner! {
                    let resolve_instance_err = resolve_instance_err;
                    let early_args_err = early_args_err;
                    let sig_import_err = sig_import_err;

                    |ccx| FnInstanceResolutionError {
                        instance: fn_instance,
                        kind: FnInstanceResolutionErrorKind::Trait {
                            resolve_instance_err: resolve_instance_err.map(Box::new),
                            early_args_err: early_args_err.map(Box::new),
                            sig_import_err
                        }
                    }
                };

                promise.and_value(sig)
            }
            FnOwner::Inherent(FnOwnerInherent {
                self_ty,
                block,
                method_idx,
            }) => {
                let fn_def = block.r(s).methods[method_idx as usize].unwrap();
                let fn_binder = fn_def.r(s).generics;

                let PromiseValue {
                    value:
                        InstantiatedImplBlock {
                            env: parent_env, ..
                        },
                    promise: resolve_block_err,
                } = self.resolve_inherent_impl_block_env(fuel, universe, block, self_ty);

                let PromiseValue {
                    value: early_args,
                    promise: early_args_err,
                } = self.obtain_fn_instance_early_args(
                    fuel,
                    universe,
                    fn_instance,
                    parent_env.clone(),
                    fn_binder,
                );

                let full_env =
                    parent_env.with_subst(GenericSubst::new(fn_def.r(s).generics, early_args));

                let PromiseValue {
                    value: sig,
                    promise: sig_import_err,
                } = self.resolve_fn_def_sig(fuel, universe, fn_def, full_env);

                let promise = typed_joiner! {
                    let resolve_block_err = resolve_block_err;
                    let early_args_err = early_args_err;
                    let sig_import_err = sig_import_err;

                    |ccx| FnInstanceResolutionError {
                        instance: fn_instance,
                        kind: FnInstanceResolutionErrorKind::Inherent {
                            resolve_block_err: resolve_block_err.map(Box::new),
                            early_args_err: early_args_err.map(Box::new),
                            sig_import_err
                        }
                    }
                };

                promise.and_value(sig)
            }
            FnOwner::AdtCtor(FnOwnerAdtCtor { ctor }) => {
                let item = ctor.r(s).owner.item(s);

                let PromiseValue {
                    value: early_args,
                    promise: early_args_err,
                } = self.obtain_fn_instance_early_args(
                    fuel,
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

                let mut import_collector = MultiPromiseBuilder::new();

                let args = tcx.intern_list(
                    &ctor
                        .r(s)
                        .fields
                        .iter()
                        .map(|field| {
                            self.importer(
                                fuel,
                                universe.clone(),
                                env.clone(),
                                ImportWfMode::ReportElsewhere,
                            )
                            .import_ty(*field.ty)
                            .flat_join(&mut import_collector)
                        })
                        .collect::<Vec<_>>(),
                );

                let sig = InstantiatedFnSig {
                    args,
                    ret_ty: self_ty,
                };

                let promise = typed_joiner! {
                    let early_args_err = early_args_err;
                    let sig_import_err = import_collector.finish();

                    |ccx| FnInstanceResolutionError {
                        instance: fn_instance,
                        kind: FnInstanceResolutionErrorKind::AdtCtor {
                            early_args_err: early_args_err.map(Box::new),
                            sig_import_err
                        }
                    }
                };

                promise.and_value(sig)
            }
        }
    }

    fn obtain_fn_instance_early_args(
        &mut self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        fn_instance: FnInstance,
        parent_env: ClauseImportEnv,
        binder: Obj<GenericBinder>,
    ) -> PromiseValue<'tcx, TyOrReList, BinderParamWfBinderError> {
        let s = self.session();

        if let Some(provided) = fn_instance.r(s).early_args {
            return PromiseValue::trivial(provided);
        }

        let early_args = self.fresh_binder_to_unconstrained_infer_params(
            universe,
            binder,
            |_ccx, idx, _generic| InferTyVarSourceInfo::LateBoundFnGeneric {
                instance: fn_instance,
                idx: idx as u32,
            },
        );

        let promise =
            self.ensure_binder_params_wf(fuel, universe, binder, parent_env, None, early_args);

        promise.and_value(early_args)
    }

    pub fn resolve_fn_def_sig(
        &mut self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        def: Obj<FnDef>,
        env: ClauseImportEnv,
    ) -> MultiPromiseValue<'tcx, InstantiatedFnSig, ImportError> {
        let s = self.session();
        let tcx = self.tcx();

        let mut collector = MultiPromiseBuilder::new();

        let output = InstantiatedFnSig {
            args: tcx.intern_list(
                &def.r(s)
                    .args
                    .r(s)
                    .iter()
                    .map(|arg| {
                        self.importer(
                            fuel,
                            universe.clone(),
                            env.clone(),
                            ImportWfMode::ReportElsewhere,
                        )
                        .import_ty(arg.ty)
                        .flat_join(&mut collector)
                    })
                    .collect::<Vec<_>>(),
            ),
            ret_ty: self
                .importer(
                    fuel,
                    universe.clone(),
                    env.clone(),
                    ImportWfMode::ReportElsewhere,
                )
                .import_ty(*def.r(s).ret_ty)
                .flat_join(&mut collector),
        };

        collector.finish().and_value(output)
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
impl<'tcx> ClauseCx<'tcx> {
    fn fresh_trait_item_to_unconstrained_trait_spec(
        &mut self,
        universe: &HrtbUniverse,
        item: Obj<TraitItem>,
    ) -> TraitSpec {
        let s = self.session();
        let tcx = self.tcx();

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
                        TyOrReKind::Re => TraitParam::Equals(TyOrRe::Re(self.fresh_re_infer())),
                        TyOrReKind::Ty => TraitParam::Equals(TyOrRe::Ty(self.fresh_ty_infer(
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
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        self_ty: Ty,
        def: Obj<FnDef>,
    ) -> PromiseValue<'tcx, FnOwner, TypeRelativeFnDefToOwnerError> {
        let s = self.session();

        match *def.r(s).owner {
            FnDefOwner::Item(_) => unreachable!(),
            FnDefOwner::TraitMethod(item, method_idx) => {
                let instance = self.fresh_trait_item_to_unconstrained_trait_spec(universe, item);

                let promise = self
                    .oblige_ty_meets_trait_instantiated(fuel, universe.clone(), self_ty, instance)
                    .map(move |_ccx, error| TypeRelativeFnDefToOwnerError::Trait {
                        item,
                        method_idx,
                        self_ty,
                        error: Box::new(error),
                    });

                promise.and_value(FnOwner::Trait(FnOwnerTrait {
                    instance,
                    self_ty,
                    method_idx,
                }))
            }
            FnDefOwner::ImplMethod(block, method_idx) => {
                PromiseValue::trivial(FnOwner::Inherent(FnOwnerInherent {
                    self_ty,
                    block,
                    method_idx,
                }))
            }
        }
    }

    pub fn fresh_impl_block(
        &mut self,
        fuel: ClauseFuel,
        universe: &HrtbUniverse,
        block: Obj<ImplItem>,
    ) -> PromiseValue<'tcx, InstantiatedImplBlock, ImplBlockSatisfyError> {
        let s = self.session();

        let mut collector = MultiPromiseBuilder::new();

        // Instantiate fresh variables for each `impl` block generic.
        let params = self.fresh_binder_to_unconstrained_infer_params(
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
            .importer(
                fuel,
                universe.clone(),
                env.clone(),
                ImportWfMode::ReportElsewhere,
            )
            .import_ty(*block.r(s).target)
            .map(move |_ccx, error| ImplBlockSatisfyErrorCulprit::SelfTyImportError(error))
            .join(&mut collector);

        env.self_ty = Some(target_ty);

        let target_trait = block.r(s).trait_.map(|trait_| {
            self.importer(
                fuel,
                universe.clone(),
                env.clone(),
                ImportWfMode::ReportElsewhere,
            )
            .import_trait_instance(target_ty, trait_)
            .map(move |_ccx, error| ImplBlockSatisfyErrorCulprit::TargetTraitImportError(error))
            .join(&mut collector)
        });

        self.ensure_binder_params_wf(
            fuel,
            universe,
            block.r(s).generics,
            env.clone(),
            None,
            params,
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
