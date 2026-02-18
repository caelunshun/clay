use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnvRef, ClauseOrigin, ClauseOriginKind, CoherenceMap, TyCtxt,
            TyFolderInfallibleExt, TyVisitorInfallibleExt, UnifyCxMode,
        },
        syntax::{
            AdtCtor, AdtItem, AdtKind, AnyGeneric, Crate, FnItem, GenericBinder, GenericSubst,
            HrtbUniverse, ImplItem, ItemKind, TraitItem, TypeAliasItem,
        },
    },
};

#[derive(Debug, Clone)]
pub struct CrateTypeckVisitor<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub coherence: &'tcx CoherenceMap,
    pub krate: Obj<Crate>,
}

impl<'tcx> CrateTypeckVisitor<'tcx> {
    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn visit_crate(&mut self) {
        let s = self.session();

        let Crate {
            name: _,
            is_local: _,
            root: _,
            items,
            lang_items: _,
        } = self.krate.r(s);

        for &item in &**items {
            match *item.r(s).kind {
                ItemKind::Module(_) => {
                    // (intentionally empty)
                }
                ItemKind::Adt(def) => {
                    self.visit_adt(def);
                }
                ItemKind::EnumVariant(_) => {
                    // (already visited in ADT checks)
                }
                ItemKind::Trait(def) => {
                    self.visit_trait(def);
                }
                ItemKind::Impl(def) => {
                    self.visit_impl(def);
                }
                ItemKind::Fn(def) => {
                    self.visit_fn_item(def);
                }
                ItemKind::TypeAlias(def) => {
                    self.visit_type_alias_item(def);
                }
            }
        }
    }

    pub fn visit_trait(&mut self, def: Obj<TraitItem>) {
        let tcx = self.tcx();
        let s = self.session();

        let TraitItem {
            item: _,
            generics,
            inherits,
            regular_generic_count: _,
            associated_types: _,
            methods,
            name_to_method: _,
        } = def.r(s);

        // Setup a `ClauseCx` with our environment in mind.
        let mut ccx = ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionAware);
        let env = ccx.import_trait_def_env_as_universal(
            &ClauseOrigin::empty_report(),
            HrtbUniverse::ROOT_REF,
            def,
        );

        // First, let's ensure that the inherited trait list is well-formed.
        {
            let inherits = ccx
                .importer(
                    &ClauseOrigin::empty_report(),
                    HrtbUniverse::ROOT,
                    env.as_ref(),
                )
                .fold_preserved(**inherits);

            ccx.wf_visitor(HrtbUniverse::ROOT)
                .with_clause_applies_to(env.self_ty)
                .visit_spanned(inherits);
        }

        // Now, let's ensure that each generic parameter's clauses are well-formed.
        self.visit_generic_binder(&mut ccx, env.as_ref(), **generics);

        // Finally, let's check method signatures and, if a default one is provided, bodies.
        for &method in methods.iter() {
            self.visit_fn_def(method);
        }

        ccx.verify();
    }

    pub fn visit_impl(&mut self, item: Obj<ImplItem>) {
        let tcx = self.tcx();
        let s = self.session();

        let ImplItem {
            item: _,
            generics,
            trait_,
            target,
            methods,
        } = item.r(s);

        // Setup a `ClauseCx` with our environment in mind.
        let mut ccx = ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionAware);
        let env = ccx.import_impl_block_env_as_universal(
            &ClauseOrigin::empty_report(),
            HrtbUniverse::ROOT_REF,
            item,
        );

        // Let's ensure that the target trait instance is well formed. This includes trait-checking
        // regular generic parameters *and* associated types.
        if let Some(trait_) = **trait_ {
            let trait_ = ccx
                .importer(
                    &ClauseOrigin::empty_report(),
                    HrtbUniverse::ROOT,
                    env.as_ref(),
                )
                .fold_preserved(trait_);

            ccx.wf_visitor(HrtbUniverse::ROOT)
                .with_clause_applies_to(env.self_ty)
                .visit_spanned(trait_);

            // Let's ensure that the type implements its super-traits as well.
            let trait_def = trait_.value.def;

            for super_clause in trait_def.r(s).inherits.iter(tcx) {
                let super_clause = ccx
                    .importer(
                        &ClauseOrigin::empty_report(),
                        HrtbUniverse::ROOT,
                        ClauseImportEnvRef::new(
                            env.self_ty,
                            &[GenericSubst {
                                binder: *trait_def.r(s).generics,
                                substs: trait_.value.params,
                            }],
                        ),
                    )
                    .fold_preserved(super_clause);

                ccx.oblige_ty_meets_clause(
                    ClauseOrigin::root_report(ClauseOriginKind::WfSuperTrait {
                        block: target.own_span(),
                        clause: super_clause.own_span(),
                    }),
                    HrtbUniverse::ROOT_REF,
                    env.self_ty,
                    super_clause.value,
                );
            }
        }

        // Let's also ensure that our target type is well-formed.
        {
            let target = ccx
                .importer(
                    &ClauseOrigin::empty_report(),
                    HrtbUniverse::ROOT,
                    env.as_ref(),
                )
                .fold_preserved(**target);

            ccx.wf_visitor(HrtbUniverse::ROOT).visit_spanned(target);
        }

        // Let's ensure that `impl` generics all have well-formed clauses.
        self.visit_generic_binder(&mut ccx, env.as_ref(), *generics);

        // Finally, let's check method signatures and bodies.
        for method in methods.iter() {
            let Some(method) = method else {
                continue;
            };

            self.visit_fn_def(*method);
        }

        ccx.verify();
    }

    pub fn visit_adt(&mut self, def: Obj<AdtItem>) {
        let s = self.session();
        let tcx = self.tcx();

        // Setup a `ClauseCx` with our environment in mind.
        let mut ccx = ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionAware);
        let env = ccx.import_adt_def_env_as_universal(
            &ClauseOrigin::empty_report(),
            HrtbUniverse::ROOT_REF,
            def,
        );

        // First, let's ensure that each generic parameter's clauses are well-formed.
        self.visit_generic_binder(&mut ccx, env.as_ref(), def.r(s).generics);

        // Now, WF-check the definition.
        match *def.r(s).kind {
            AdtKind::Struct(kind) => {
                self.visit_adt_ctor(&mut ccx, env.as_ref(), *kind.r(s).ctor);
            }
            AdtKind::Enum(kind) => {
                for variant in kind.r(s).variants.iter() {
                    self.visit_adt_ctor(&mut ccx, env.as_ref(), *variant.r(s).ctor);
                }
            }
        }

        ccx.verify();
    }

    fn visit_adt_ctor(
        &mut self,
        ccx: &mut ClauseCx,
        env: ClauseImportEnvRef<'_>,
        ctor: Obj<AdtCtor>,
    ) {
        let s = self.session();

        for field in ctor.r(s).fields.iter() {
            let field_ty = ccx
                .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                .fold_preserved(*field.ty);

            ccx.wf_visitor(HrtbUniverse::ROOT).visit_spanned(field_ty);
        }
    }

    pub fn visit_fn_item(&mut self, def: Obj<FnItem>) {
        let s = self.session();

        self.visit_fn_def(*def.r(s).def);
    }

    pub fn visit_type_alias_item(&mut self, def: Obj<TypeAliasItem>) {
        let tcx = self.tcx();
        let s = self.session();

        // Setup a `ClauseCx` with our environment in mind.
        let mut ccx = ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionAware);
        let env = ccx.import_type_alias_def_env_as_universal(
            &ClauseOrigin::empty_report(),
            HrtbUniverse::ROOT_REF,
            def,
        );

        // First, let's ensure that each generic parameter's clauses are well-formed.
        self.visit_generic_binder(&mut ccx, env.as_ref(), def.r(s).generics);

        // Now, WF-check the definition.
        let body = ccx
            .importer(
                &ClauseOrigin::empty_report(),
                HrtbUniverse::ROOT,
                env.as_ref(),
            )
            .fold_preserved(*def.r(s).body);

        ccx.wf_visitor(HrtbUniverse::ROOT).visit_spanned(body);

        ccx.verify();
    }

    pub fn visit_generic_binder(
        &mut self,
        ccx: &mut ClauseCx,
        env: ClauseImportEnvRef<'_>,
        generics: Obj<GenericBinder>,
    ) {
        let s = self.session();

        for &generic in &generics.r(s).defs {
            let clauses = match generic {
                AnyGeneric::Re(generic) => *generic.r(s).clauses,
                AnyGeneric::Ty(generic) => *generic.r(s).clauses,
            };

            let clauses = ccx
                .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                .fold_preserved(clauses);

            ccx.wf_visitor(HrtbUniverse::ROOT)
                .with_clause_applies_to(env.self_ty)
                .visit_spanned(clauses);
        }
    }
}
