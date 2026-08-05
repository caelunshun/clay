//! Utilities for instantiating fresh universal or existential type objects.

use crate::{
    base::arena::{HasInterner as _, HasListInterner as _, Obj},
    semantic::{
        infer::{
            ClauseCx, ClauseImportEnv, GenericSubst, HrtbUniverse, ObligeCause, SigImporterWfMode,
        },
        syntax::{
            AdtInstance, AdtItem, AnyGeneric, FnDef, FnDefOwner, FnInstance, FnInstanceInner,
            FnOwner, FnOwnerAdtCtor, FnOwnerInherent, FnOwnerTrait, GenericBinder, HrtbBinder,
            ImplItem, InferTyVarSourceInfo, RelationMode, TraitClause, TraitInstance, TraitItem,
            TraitParam, TraitSpec, Ty, TyKind, TyList, TyOrRe, TyOrReList, TypeAliasItem,
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

// Machinery
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
                            // TODO: Can we really skip WF here?
                            .import_clause_no_spec_wf(clause);

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
                        // TODO: Can we really skip WF here?
                        .import_clause_list_no_spec_wf(*generic.r(s).clauses);

                    self.ccx
                        .init_ty_universal_var_direct_clauses(target, clauses);
                }
                _ => unreachable!(),
            }
        }
    }
}

// Specialized
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
///
/// Do not use these methods unless you intend to instantiate and later constrain an inference
/// variable. For example, it would be wrong to attempt to WF-check a function instance without any
/// early-bound parameters by importing it here because, although the inference variables would be
/// properly constrained as to ensure well-formedness, those variables would never be constrained
/// during WF checking, leading to unsatisfied obligation errors. Ask me how I know.
pub struct ClauseCxInferInstantiation<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
}

// Machinery
impl<'tcx> ClauseCxInferInstantiation<'_, 'tcx> {
    pub fn binder_to_constrained_vars(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        binder_parent_env: &ClauseImportEnv,
        binder: Obj<GenericBinder>,
    ) -> TyOrReList {
        let substs = self.binder_to_unconstrained_vars(universe, binder);
        self.ccx
            .init_constraints_for_binder(cause, universe, binder_parent_env, binder, substs);
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
}

// Specialized
impl ClauseCxInferInstantiation<'_, '_> {
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
            FnDefOwner::ImplMethod(block, method_idx) => FnOwner::Inherent(FnOwnerInherent {
                self_ty,
                block,
                method_idx,
            }),
            FnDefOwner::TraitMethod(trait_item, method_idx) => {
                let params = self.binder_to_constrained_vars(
                    cause,
                    HrtbUniverse::ROOT_REF,
                    &ClauseImportEnv::new(Some(self_ty), []),
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

                FnOwner::Trait(FnOwnerTrait {
                    instance: TraitSpec {
                        def: trait_item,
                        params,
                    },
                    self_ty,
                    method_idx,
                })
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
            FnOwner::Item(_) => ClauseImportEnv::new(None, []),
            FnOwner::Trait(FnOwnerTrait {
                instance,
                self_ty,
                method_idx: _,
            }) => {
                let instance = self.instantiate_trait_spec(cause, universe, self_ty, instance);

                ClauseImportEnv::new(
                    Some(self_ty),
                    [GenericSubst::new(
                        *instance.def.r(s).generics,
                        instance.params,
                    )],
                )
            }
            FnOwner::Inherent(FnOwnerInherent {
                self_ty,
                block,
                method_idx: _,
            }) => {
                let block_params = self.binder_to_constrained_vars(
                    cause,
                    universe,
                    &ClauseImportEnv::new(Some(self_ty), []),
                    block.r(s).generics,
                );

                let block_env = ClauseImportEnv::new(
                    Some(self_ty),
                    [GenericSubst::new(block.r(s).generics, block_params)],
                );

                let expected_self_ty = self
                    .ccx
                    .importer(
                        cause.clone(),
                        universe.clone(),
                        block_env.clone(),
                        SigImporterWfMode::DelayBug,
                    )
                    .import_ty(*block.r(s).target);

                self.ccx.oblige_ty_unifies_ty(
                    cause.clone(),
                    self_ty,
                    expected_self_ty,
                    RelationMode::Equate,
                );

                block_env
            }
            // FIXME: this is not how one instantiates this environment—we should instantiate
            // anything because that's the instance's job.
            FnOwner::AdtCtor(owner @ FnOwnerAdtCtor { ctor }) => {
                let args = self.binder_to_constrained_vars(
                    cause,
                    universe,
                    // No parent environment exists for these generics.
                    &ClauseImportEnv::new(None, []),
                    owner.early_generics(s),
                );

                let self_ty = tcx.intern(TyKind::Adt(AdtInstance {
                    def: ctor.r(s).owner.item(s),
                    params: args,
                }));

                ClauseImportEnv::new(
                    Some(self_ty),
                    [GenericSubst::new(owner.early_generics(s), args)],
                )
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
        let early_generics = owner.early_generics(s);

        env.substs.push(GenericSubst::new(
            early_generics,
            if let Some(early_args) = early_args {
                early_args
            } else {
                self.binder_to_constrained_vars(cause, universe, &env, early_generics)
            },
        ));

        env
    }
}

// === Misc Helpers === //

impl ClauseCx<'_> {
    pub fn import_fn_owner_receiver_as_infer(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        env: &ClauseImportEnv,
        def: FnOwner,
    ) -> Ty {
        let s = self.session();
        let tcx = self.tcx();

        debug_assert!(def.has_self_parameter(s));

        // self.importer(
        //     cause.clone(),
        //     universe.clone(),
        //     env.clone(),
        //     SigImporterWfMode::DelayBug,
        // )
        // .import_ty(def.unimported_sig_args(tcx).r(s)[0])

        todo!()
    }

    pub fn import_fn_owner_sig(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        env: &ClauseImportEnv,
        def: FnOwner,
    ) -> (TyList, Ty) {
        let tcx = self.tcx();

        // let args = self
        //     .importer()
        //     .with_expansion_cause(cause.clone())
        //     .import_report_elsewhere(universe, env, def.unimported_sig_args(tcx));
        //
        // let ret_ty = self
        //     .importer()
        //     .with_expansion_cause(cause.clone())
        //     .import_report_elsewhere(universe, env, def.unimported_sig_ret_ty(tcx));
        //
        // (args, ret_ty)

        todo!()
    }
}
