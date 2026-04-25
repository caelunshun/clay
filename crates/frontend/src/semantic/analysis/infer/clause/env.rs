use crate::{
    base::{
        arena::{HasInterner as _, HasListInterner as _, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnv, ClauseImportEnvRef, ClauseOrigin, ClauseOriginKind,
            HrtbUniverse,
        },
        syntax::{
            AdtInstance, AdtItem, AnyGeneric, FnDef, FnDefOwner, FnInstance, FnInstanceInner,
            FnOwner, GenericBinder, GenericSubst, HrtbBinder, HrtbBinderKind, ImplItem,
            InferTyVarSourceInfo, RelationMode, SpannedTraitClauseView, TraitClause, TraitItem,
            TraitParam, TraitSpec, Ty, TyFolderInfallibleExt as _, TyKind, TyList, TyOrRe,
            TypeAliasItem, UniversalReVarSourceInfo, UniversalTyVarSourceInfo,
        },
    },
};

impl<'tcx> ClauseCx<'tcx> {
    // === Universal === //

    pub fn import_binder_list_as_universal(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        self_ty: Ty,
        binders: &[Obj<GenericBinder>],
    ) -> Vec<GenericSubst> {
        let substs = self.create_blank_universal_vars_from_binder_list(universe, binders);

        self.init_universal_var_clauses_from_binder(
            origin,
            universe,
            ClauseImportEnvRef {
                self_ty,
                sig_generic_substs: &substs,
            },
        );

        substs
    }

    pub fn create_blank_universal_vars_from_binder_list(
        &mut self,
        universe: &HrtbUniverse,
        binders: &[Obj<GenericBinder>],
    ) -> Vec<GenericSubst> {
        binders
            .iter()
            .map(|&binder| self.create_blank_universal_vars_from_binder(universe, binder))
            .collect()
    }

    pub fn create_blank_universal_vars_from_binder(
        &mut self,
        universe: &HrtbUniverse,
        binder: Obj<GenericBinder>,
    ) -> GenericSubst {
        let s = self.session();
        let tcx = self.tcx();

        let substs =
            binder
                .r(s)
                .defs
                .iter()
                .map(|&generic| match generic {
                    AnyGeneric::Re(generic) => {
                        TyOrRe::Re(self.fresh_re_universal(UniversalReVarSourceInfo::Root(generic)))
                    }
                    AnyGeneric::Ty(generic) => TyOrRe::Ty(self.fresh_ty_universal(
                        universe.clone(),
                        UniversalTyVarSourceInfo::Root(generic),
                    )),
                })
                .collect::<Vec<_>>();

        let substs = tcx.intern_list(&substs);

        GenericSubst { binder, substs }
    }

    pub fn init_universal_var_clauses_from_binder(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        env: ClauseImportEnvRef<'_>,
    ) {
        let s = self.session();

        for &subst in env.sig_generic_substs {
            for (&generic, &subst) in subst.binder.r(s).defs.iter().zip(subst.substs.r(s)) {
                match (generic, subst) {
                    (AnyGeneric::Re(generic), TyOrRe::Re(target)) => {
                        for &clause in generic.r(s).clauses.value.r(s) {
                            let clause = self.importer(origin, universe.clone(), env).fold(clause);

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
                    (AnyGeneric::Ty(generic), TyOrRe::Ty(target)) => {
                        let TyKind::UniversalVar(target) = *target.r(s) else {
                            unreachable!()
                        };

                        let clauses = self
                            .importer(origin, universe.clone(), env)
                            .fold(generic.r(s).clauses.value);

                        self.init_ty_universal_var_direct_clauses(target, clauses);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    // === Specialized universal imports === //

    pub fn import_trait_def_env_as_universal(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        def: Obj<TraitItem>,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        // Create a universal variable representing `Self`
        let self_var =
            self.fresh_ty_universal_var(universe.clone(), UniversalTyVarSourceInfo::TraitSelf);

        let self_ty = tcx.intern(TyKind::UniversalVar(self_var));

        // Create universal variables for each parameter.
        let sig_generic_substs =
            self.import_binder_list_as_universal(origin, universe, self_ty, &[*def.r(s).generics]);

        let generic_params = sig_generic_substs[0].substs;

        // Make `Self` implement the trait with these synthesized parameters.
        self.init_ty_universal_var_direct_clauses(
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

        ClauseImportEnv::new(self_ty, sig_generic_substs)
    }

    pub fn import_adt_def_env_as_universal(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        def: Obj<AdtItem>,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        // Create universal parameters.
        let sig_generic_substs =
            self.create_blank_universal_vars_from_binder_list(universe, &[def.r(s).generics]);

        // Create the `Self` type.
        let self_ty = tcx.intern(TyKind::Adt(AdtInstance {
            def,
            params: sig_generic_substs[0].substs,
        }));

        // Initialize the clauses.
        self.init_universal_var_clauses_from_binder(
            origin,
            universe,
            ClauseImportEnvRef {
                self_ty,
                sig_generic_substs: &sig_generic_substs,
            },
        );

        ClauseImportEnv::new(self_ty, sig_generic_substs)
    }

    pub fn import_impl_block_env_as_universal(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        def: Obj<ImplItem>,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        // Create universal parameters.
        let sig_generic_substs =
            self.create_blank_universal_vars_from_binder_list(universe, &[def.r(s).generics]);

        // Create the `Self` type. This type cannot contain `Self` so we give a dummy self type.
        let self_ty = self
            .importer(
                origin,
                universe.clone(),
                ClauseImportEnvRef::new(tcx.intern(TyKind::SigThis), &sig_generic_substs),
            )
            .fold(def.r(s).target.value);

        // Initialize the clauses.
        self.init_universal_var_clauses_from_binder(
            origin,
            universe,
            ClauseImportEnvRef::new(self_ty, &sig_generic_substs),
        );

        ClauseImportEnv::new(self_ty, sig_generic_substs)
    }

    pub fn import_fn_item_generics_as_universal(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        self_ty: Ty,
        def: Obj<FnDef>,
    ) -> Vec<GenericSubst> {
        self.import_binder_list_as_universal(
            origin,
            universe,
            self_ty,
            &[def.r(self.session()).generics],
        )
    }

    pub fn import_fn_def_env_as_universal(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        def: Obj<FnDef>,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        let mut env = match *def.r(s).owner {
            FnDefOwner::Item(_item) => ClauseImportEnv {
                self_ty: tcx.intern(TyKind::SigThis),
                sig_generic_substs: Vec::new(),
            },
            FnDefOwner::TraitMethod(def, _idx) => {
                self.import_trait_def_env_as_universal(origin, universe, def)
            }
            FnDefOwner::ImplMethod(def, _idx) => {
                self.import_impl_block_env_as_universal(origin, universe, def)
            }
        };

        env.sig_generic_substs
            .extend_from_slice(&self.import_fn_item_generics_as_universal(
                origin,
                universe,
                env.self_ty,
                def,
            ));

        env
    }

    pub fn import_type_alias_def_env_as_universal(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        def: Obj<TypeAliasItem>,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        let this_ty = tcx.intern(TyKind::SigThis);

        ClauseImportEnv::new(
            this_ty,
            self.import_binder_list_as_universal(origin, universe, this_ty, &[def.r(s).generics]),
        )
    }

    // === Existential === //

    pub fn instantiate_binder_list_as_infer(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        mut base_env: ClauseImportEnv,
        binders: &[Obj<GenericBinder>],
    ) -> ClauseImportEnv {
        // Produce a substitution for each binder.
        let substs = self.instantiate_blank_infer_vars_from_binder_list(universe, binders);
        base_env.sig_generic_substs.extend_from_slice(&substs);

        // Register clause obligations.
        self.oblige_import_env_meets_own_binder_clauses(origin, universe, base_env.as_ref());

        base_env
    }

    pub fn instantiate_blank_infer_vars_from_binder_list(
        &mut self,
        universe: &HrtbUniverse,
        binders: &[Obj<GenericBinder>],
    ) -> Vec<GenericSubst> {
        binders
            .iter()
            .map(|&binder| self.instantiate_blank_infer_vars_from_binder(universe, binder))
            .collect()
    }

    pub fn instantiate_blank_infer_vars_from_binder(
        &mut self,
        universe: &HrtbUniverse,
        binder: Obj<GenericBinder>,
    ) -> GenericSubst {
        let s = self.session();
        let tcx = self.tcx();

        let substs =
            binder
                .r(s)
                .defs
                .iter()
                .map(|&generic| match generic {
                    AnyGeneric::Re(_) => TyOrRe::Re(self.fresh_re_infer()),
                    AnyGeneric::Ty(_) => TyOrRe::Ty(self.fresh_ty_infer(
                        universe.clone(),
                        InferTyVarSourceInfo::UniversalElabHelper,
                    )),
                })
                .collect::<Vec<_>>();

        let substs = tcx.intern_list(&substs);

        GenericSubst { binder, substs }
    }

    pub fn oblige_import_env_meets_own_binder_clauses(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        env: ClauseImportEnvRef<'_>,
    ) {
        let s = self.session();

        for &subst in env.sig_generic_substs {
            self.oblige_args_meet_binder_clauses(
                universe,
                env,
                &subst.binder.r(s).defs,
                subst.substs.r(s),
                |_this, _idx, clause| {
                    origin
                        .clone()
                        .child(ClauseOriginKind::GenericRequirements { clause })
                },
            );
        }
    }

    pub fn oblige_args_meet_binder_clauses(
        &mut self,
        universe: &HrtbUniverse,
        def_env: ClauseImportEnvRef<'_>,
        defs: &[AnyGeneric],
        args: &[TyOrRe],
        mut gen_origin: impl FnMut(&mut Self, usize, Span) -> ClauseOrigin,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        for (i, (&generic, &subst)) in defs.iter().zip(args).enumerate() {
            match (generic, subst) {
                (AnyGeneric::Re(generic), TyOrRe::Re(target)) => {
                    for clause in generic.r(s).clauses.iter(tcx) {
                        let clause_span = clause.own_span();

                        let SpannedTraitClauseView::Outlives(must_outlive_dir, must_outlive) =
                            clause.view(tcx)
                        else {
                            unreachable!()
                        };

                        let origin = gen_origin(self, i, clause_span);

                        let must_outlive = self
                            .importer(&origin, universe.clone(), def_env)
                            .fold_preserved(must_outlive);

                        self.oblige_general_outlives(
                            origin,
                            TyOrRe::Re(target),
                            must_outlive.value,
                            must_outlive_dir,
                        );
                    }
                }
                (AnyGeneric::Ty(generic), TyOrRe::Ty(target)) => {
                    for clause in generic.r(s).clauses.iter(tcx) {
                        let origin = gen_origin(self, i, clause.own_span());

                        let clause = self
                            .importer(&origin, universe.clone(), def_env)
                            .fold_preserved(clause);

                        match clause.value {
                            TraitClause::Outlives(must_outlive_dir, must_outlive) => {
                                self.oblige_general_outlives(
                                    origin,
                                    TyOrRe::Ty(target),
                                    must_outlive,
                                    must_outlive_dir,
                                );
                            }
                            TraitClause::Trait(rhs) => {
                                self.oblige_ty_meets_trait(origin, universe.clone(), target, rhs);
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    // === Specialized existential imports === //

    pub fn instantiate_fn_def_as_blank_owner_infer(
        &mut self,
        def: Obj<FnDef>,
        self_ty: Ty,
    ) -> FnOwner {
        let s = self.session();
        let tcx = self.tcx();

        match *def.r(s).owner {
            FnDefOwner::Item(_) => unreachable!(),
            FnDefOwner::ImplMethod(block, method_idx) => FnOwner::Inherent {
                self_ty,
                block,
                method_idx,
            },
            FnDefOwner::TraitMethod(trait_item, method_idx) => {
                let params = self
                    .instantiate_blank_infer_vars_from_binder(
                        HrtbUniverse::ROOT_REF,
                        *trait_item.r(s).generics,
                    )
                    .substs;

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

    pub fn instantiate_fn_owner_env_as_infer(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        owner: FnOwner,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        match owner {
            FnOwner::Item(_) => ClauseImportEnv::new(tcx.intern(TyKind::SigThis), Vec::new()),
            FnOwner::Trait {
                instance,
                self_ty,
                method_idx: _,
            } => {
                let substs = instance
                    .params
                    .r(s)
                    .iter()
                    .map(|&param| match param {
                        TraitParam::Equals(value) => value,
                        TraitParam::Unspecified(clauses) => {
                            let ty = self.fresh_ty_infer(
                                universe.clone(),
                                InferTyVarSourceInfo::TraitAssocPlaceholderHelper,
                            );
                            self.oblige_ty_meets_clauses(origin, universe, ty, clauses);

                            TyOrRe::Ty(ty)
                        }
                    })
                    .collect::<Vec<_>>();

                let substs = tcx.intern_list(&substs);

                let params = substs
                    .r(s)
                    .iter()
                    .copied()
                    .map(TraitParam::Equals)
                    .collect::<Vec<_>>();

                let params = tcx.intern_list(&params);

                self.oblige_ty_meets_trait_instantiated(
                    origin.clone(),
                    universe.clone(),
                    self_ty,
                    TraitSpec {
                        def: instance.def,
                        params,
                    },
                );

                ClauseImportEnv::new(
                    self_ty,
                    vec![GenericSubst {
                        binder: *instance.def.r(s).generics,
                        substs,
                    }],
                )
            }
            FnOwner::Inherent {
                self_ty,
                block,
                method_idx: _,
            } => {
                let env = self.instantiate_binder_list_as_infer(
                    origin,
                    universe,
                    ClauseImportEnv::new(self_ty, Vec::new()),
                    &[block.r(s).generics],
                );

                let expected_self_ty = self
                    .importer(origin, universe.clone(), env.as_ref())
                    .fold(block.r(s).target.value);

                self.oblige_ty_unifies_ty(
                    origin.clone(),
                    self_ty,
                    expected_self_ty,
                    RelationMode::Equate,
                );

                env
            }
        }
    }

    pub fn instantiate_fn_instance_env_as_infer(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        instance: FnInstance,
    ) -> ClauseImportEnv {
        let s = self.session();

        let FnInstanceInner { owner, early_args } = *instance.r(s);

        let mut env = self.instantiate_fn_owner_env_as_infer(origin, universe, owner);
        let def = owner.def(s);

        if let Some(early_args) = early_args {
            env.sig_generic_substs.push(GenericSubst {
                binder: def.r(s).generics,
                substs: early_args,
            });
        } else {
            env =
                self.instantiate_binder_list_as_infer(origin, universe, env, &[def.r(s).generics]);
        }

        env
    }

    pub fn import_fn_instance_receiver_as_infer(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        env: ClauseImportEnvRef<'_>,
        def: Obj<FnDef>,
    ) -> Ty {
        let s = self.session();

        debug_assert!(*def.r(s).has_self_param);

        self.importer(origin, universe.clone(), env)
            .fold(def.r(s).args.r(s)[0].ty.value)
    }

    pub fn import_fn_instance_sig(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        env: ClauseImportEnvRef<'_>,
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

        let args = self.importer(origin, universe.clone(), env).fold(args);
        let ret_ty = self
            .importer(origin, universe.clone(), env)
            .fold(def.r(s).ret_ty.value);

        (args, ret_ty)
    }
}
