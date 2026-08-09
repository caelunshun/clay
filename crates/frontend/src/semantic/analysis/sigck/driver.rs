use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::typeck::type_check_function,
        infer::{
            ClauseCx, ClauseImportEnv, CoherenceMap, GenericSubst, HrtbUniverse, ObligeCause,
            ObligeCauseOrigin, UnifyCxMode,
        },
        syntax::{
            AdtCtor, AdtItem, AdtKind, AnyGeneric, Crate, FnItem, GenericBinder, ImplItem,
            ItemKind, TraitItem, TyCtxt, TypeAliasItem,
        },
    },
};

#[derive(Debug, Clone)]
pub struct CrateSigckVisitor<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub coherence: &'tcx CoherenceMap,
    pub krate: Obj<Crate>,
}

impl<'tcx> CrateSigckVisitor<'tcx> {
    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn visit_crate(&mut self) {
        let s = self.session();

        for &item in &**self.krate.r(s).items {
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
        let env = ccx.instantiate_universal().env_for_trait_def(
            &ObligeCause::new_empty_report(),
            HrtbUniverse::ROOT_REF,
            def,
        );

        // First, let's ensure that the inherited trait list is well-formed.
        ccx.import_report_here(&env, **inherits);

        // Now, let's ensure that each generic parameter's clauses are well-formed.
        self.visit_generic_binder(&mut ccx, &env, **generics);

        // Finally, let's check method signatures and, if a default one is provided, bodies.
        for &method in methods.iter() {
            type_check_function(self, method);
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
        let env = ccx.instantiate_universal().env_for_impl_block(
            &ObligeCause::new_empty_report(),
            HrtbUniverse::ROOT_REF,
            item,
        );

        // Let's ensure that the target trait instance is well formed. This includes trait-checking
        // regular generic parameters *and* associated types.
        if let Some(trait_) = **trait_ {
            let base_trait_instance = ccx
                .importer_here(&env)
                .import_trait_instance(env.unwrap_self_ty(), trait_);

            // Let's ensure that the type implements its super-traits as well.
            let trait_def = trait_.def;

            let trait_env = ClauseImportEnv::new(
                Some(env.unwrap_self_ty()),
                [GenericSubst::new(
                    *trait_def.r(s).generics,
                    base_trait_instance.params,
                )],
            );

            for &super_clause in trait_def.r(s).inherits.elems.r(s) {
                let super_clause_span = super_clause.span;
                let super_clause = ccx.import_report_elsewhere(&trait_env, super_clause);

                ccx.oblige_ty_meets_clause(
                    ObligeCause::new_report(ObligeCauseOrigin::HirCheckSuperTrait {
                        block: target.r(s).span,
                        clause: super_clause_span,
                    }),
                    HrtbUniverse::ROOT_REF,
                    env.unwrap_self_ty(),
                    super_clause,
                );
            }
        }

        // Let's also ensure that our target type is well-formed.
        ccx.import_report_here(&env, **target);

        // Let's ensure that `impl` generics all have well-formed clauses.
        self.visit_generic_binder(&mut ccx, &env, *generics);

        // Finally, let's check method signatures and bodies.
        for method in methods.iter() {
            let Some(method) = method else {
                continue;
            };

            type_check_function(self, *method);
        }

        ccx.verify();
    }

    pub fn visit_adt(&mut self, def: Obj<AdtItem>) {
        let s = self.session();
        let tcx = self.tcx();

        // Setup a `ClauseCx` with our environment in mind.
        let mut ccx = ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionAware);
        let env = ccx.instantiate_universal().env_for_adt_def(
            &ObligeCause::new_empty_report(),
            HrtbUniverse::ROOT_REF,
            def,
        );

        // First, let's ensure that each generic parameter's clauses are well-formed.
        self.visit_generic_binder(&mut ccx, &env, def.r(s).generics);

        // Now, WF-check the definition.
        match *def.r(s).kind {
            AdtKind::Struct(kind) => {
                self.visit_adt_ctor(&mut ccx, &env, *kind.r(s).ctor);
            }
            AdtKind::Enum(kind) => {
                for variant in kind.r(s).variants.iter() {
                    self.visit_adt_ctor(&mut ccx, &env, *variant.r(s).ctor);
                }
            }
        }

        ccx.verify();
    }

    fn visit_adt_ctor(&mut self, ccx: &mut ClauseCx, env: &ClauseImportEnv, ctor: Obj<AdtCtor>) {
        let s = self.session();

        for field in ctor.r(s).fields.iter() {
            ccx.import_report_here(env, *field.ty);
        }
    }

    pub fn visit_fn_item(&mut self, def: Obj<FnItem>) {
        let s = self.session();

        type_check_function(self, *def.r(s).def);
    }

    pub fn visit_type_alias_item(&mut self, def: Obj<TypeAliasItem>) {
        let tcx = self.tcx();
        let s = self.session();

        // Setup a `ClauseCx` with our environment in mind.
        let mut ccx = ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionAware);
        let env = ccx.instantiate_universal().env_for_type_alias_def(
            &ObligeCause::new_empty_report(),
            HrtbUniverse::ROOT_REF,
            def,
        );

        // First, let's ensure that each generic parameter's clauses are well-formed.
        self.visit_generic_binder(&mut ccx, &env, def.r(s).generics);

        // Now, WF-check the definition.
        ccx.import_report_here(&env, *def.r(s).body);

        ccx.verify();
    }

    pub fn visit_generic_binder(
        &mut self,
        ccx: &mut ClauseCx,
        env: &ClauseImportEnv,
        generics: Obj<GenericBinder>,
    ) {
        let s = self.session();

        for &generic in &generics.r(s).defs {
            let clauses = match generic {
                AnyGeneric::Re(generic) => *generic.r(s).clauses,
                AnyGeneric::Ty(generic) => *generic.r(s).clauses,
            };

            ccx.import_report_here(env, clauses);
        }
    }
}
