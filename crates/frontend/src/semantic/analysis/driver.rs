use crate::{
    base::{Obj, Session},
    semantic::{
        infer::{
            ClauseCx, ClauseFuel, ClauseImportEnv, GenericSubst, HrtbUniverse, ImplCache,
            SpannedError, UnifyCxMode,
        },
        syntax::{
            AdtCtor, AdtItem, AdtKind, AnyGeneric, Crate, FnDef, FnItem, GenericBinder, ImplItem,
            ItemKind, LangItems, TraitItem, TypeAliasItem,
        },
    },
};

pub struct TyCtxt<'a> {
    pub session: &'a Session,
    pub impl_cache: &'a ImplCache,
    pub lang_items: &'a LangItems,
}

impl<'a> TyCtxt<'a> {
    pub fn session(&self) -> &'a Session {
        self.session
    }

    pub fn check_crate(&self, krate: Obj<Crate>) {
        let s = self.session();

        for &item in &**krate.r(s).items {
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
                    self.check_trait(def);
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

    pub fn check_trait(&self, def: Obj<TraitItem>) {
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
        let mut ccx = ClauseCx::new(self, UnifyCxMode::RegionAware);
        let env = ccx.universal_env_for_trait_def(def);

        // First, let's ensure that the inherited trait list is well-formed.
        ccx.import_here(&env, **inherits);

        // Now, let's ensure that each generic parameter's clauses are well-formed.
        self.visit_generic_binder(&mut ccx, &env, **generics);

        // Finally, let's check method signatures and, if a default one is provided, bodies.
        for &method in methods.iter() {
            self.visit_fn_def(method);
        }

        ccx.verify();
    }

    pub fn visit_impl(&self, item: Obj<ImplItem>) {
        let s = self.session();

        let ImplItem {
            item: _,
            generics,
            trait_,
            target,
            methods,
        } = item.r(s);

        // Setup a `ClauseCx` with our environment in mind.
        let mut ccx = ClauseCx::new(self, UnifyCxMode::RegionAware);
        let env = ccx.universal_env_for_impl_block(item);

        // Let's ensure that the target trait instance is well formed. This includes trait-checking
        // regular generic parameters *and* associated types.
        if let Some(trait_) = **trait_ {
            let base_trait_instance = ccx
                .importer_here(&env)
                .import_trait_instance(env.unwrap_self_ty(), trait_)
                .report_loud();

            // Let's ensure that the type implements its super-traits as well.
            let trait_env = ClauseImportEnv::new(
                Some(env.unwrap_self_ty()),
                [GenericSubst::new(
                    *trait_.def.r(s).generics,
                    base_trait_instance.params,
                )],
            );

            for &super_clause in trait_.def.r(s).inherits.elems.r(s) {
                let super_clause_span = super_clause.span;
                let super_clause = ccx.import_elsewhere(&trait_env, super_clause);

                ccx.oblige_ty_meets_clause(
                    ClauseFuel::new(),
                    HrtbUniverse::ROOT_REF,
                    env.unwrap_self_ty(),
                    super_clause,
                )
                .map(move |_ccx, error| SpannedError(super_clause_span, error))
                .report_loud();
            }
        }

        // Let's also ensure that our target type is well-formed.
        ccx.import_here(&env, **target);

        // Let's ensure that `impl` generics all have well-formed clauses.
        self.visit_generic_binder(&mut ccx, &env, *generics);

        // Finally, let's check method signatures and bodies.
        for method in methods.iter() {
            let Some(method) = method else {
                continue;
            };

            self.visit_fn_def(*method);
        }

        ccx.verify();
    }

    pub fn visit_adt(&self, def: Obj<AdtItem>) {
        let s = self.session();

        // Setup a `ClauseCx` with our environment in mind.
        let mut ccx = ClauseCx::new(self, UnifyCxMode::RegionAware);
        let env = ccx.universal_env_for_adt_def(def);

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

    fn visit_adt_ctor(&self, ccx: &mut ClauseCx, env: &ClauseImportEnv, ctor: Obj<AdtCtor>) {
        let s = self.session();

        for field in ctor.r(s).fields.iter() {
            ccx.import_here(env, *field.ty);
        }
    }

    pub fn visit_fn_item(&self, def: Obj<FnItem>) {
        let s = self.session();

        self.visit_fn_def(*def.r(s).def);
    }

    pub fn visit_type_alias_item(&self, def: Obj<TypeAliasItem>) {
        let s = self.session();

        // Setup a `ClauseCx` with our environment in mind.
        let mut ccx = ClauseCx::new(self, UnifyCxMode::RegionAware);
        let env = ccx.universal_env_for_type_alias_def(def);

        // First, let's ensure that each generic parameter's clauses are well-formed.
        self.visit_generic_binder(&mut ccx, &env, def.r(s).generics);

        // Now, WF-check the definition.
        ccx.import_here(&env, *def.r(s).body);

        ccx.verify();
    }

    pub fn visit_generic_binder(
        &self,
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

            ccx.import_here(env, clauses);
        }
    }

    pub fn visit_fn_def(&self, def: Obj<FnDef>) {
        self.type_check_function(def);
        self.build_function_mir(def);
        self.run_borrow_check(def);
    }
}
