use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::{
            ClauseCx, CoherenceMap, TyCtxt, TyFolderInfalliblePreservesSpans as _,
            TyVisitorInfallibleExt, UnifyCxMode,
        },
        syntax::{
            AdtCtor, AdtItem, AdtKind, AnyGeneric, Crate, FuncItem, GenericBinder, GenericSubst,
            ImplItem, ItemKind, TraitItem, Ty,
        },
    },
};

#[derive(Debug, Clone)]
pub struct CrateTypeckVisitor<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub coherence: &'tcx CoherenceMap,
}

impl<'tcx> CrateTypeckVisitor<'tcx> {
    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn visit_crate(&mut self, krate: Obj<Crate>) {
        let s = self.session();

        let Crate {
            name: _,
            is_local: _,
            root: _,
            items,
        } = krate.r(s);

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
                ItemKind::Func(def) => {
                    self.visit_fn_item(def);
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
        } = def.r(s);

        // Setup a `ClauseCx` with our environment in mind.
        let mut ccx = ClauseCx::new(tcx, self.coherence, UnifyCxMode::RegionAware);
        let env = ccx.import_trait_def_env(def);

        // First, let's ensure that the inherited trait list is well-formed.
        {
            let inherits = ccx
                .importer(env.self_ty, &env.sig_generic_substs)
                .fold_spanned_clause_list(**inherits);

            ccx.wf_visitor()
                .with_clause_applies_to(env.self_ty)
                .visit_spanned(inherits);
        }

        // Now, let's ensure that each generic parameter's clauses are well-formed.
        self.visit_generic_binder(&mut ccx, env.self_ty, &env.sig_generic_substs, *generics);

        // Finally, let's check method signatures and, if a default one is provided, bodies.
        // TODO
        // for method in methods.iter() {
        //     self.visit_fn_def(method.r(s).func)?;
        // }
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
        let mut ccx = ClauseCx::new(tcx, self.coherence, UnifyCxMode::RegionAware);
        let env = ccx.import_impl_block_env(item);

        // Let's ensure that the target trait instance is well formed.
        if let Some(trait_) = *trait_ {
            let mut ccx = ClauseCx::new(self.tcx(), self.coherence, UnifyCxMode::RegionAware);

            let trait_ = ccx
                .importer(env.self_ty, &env.sig_generic_substs)
                .fold_spanned_trait_instance(trait_);

            ccx.wf_visitor()
                .with_clause_applies_to(env.self_ty)
                .visit_spanned(trait_);
        }

        // Let's also ensure that our target type is well-formed.
        {
            let target = ccx
                .importer(env.self_ty, &env.sig_generic_substs)
                .fold_spanned_ty(*target);

            ccx.wf_visitor().visit_spanned(target);
        }

        // Let's ensure that `impl` generics all have well-formed clauses.
        self.visit_generic_binder(&mut ccx, env.self_ty, &env.sig_generic_substs, *generics);

        // Finally, let's check method signatures and bodies.
        // TODO
        // for method in methods.iter() {
        //     self.visit_fn_def(*method)?;
        // }
    }

    pub fn visit_adt(&mut self, def: Obj<AdtItem>) {
        let s = self.session();
        let tcx = self.tcx();

        // Setup a `ClauseCx` with our environment in mind.
        let mut ccx = ClauseCx::new(tcx, self.coherence, UnifyCxMode::RegionAware);
        let env = ccx.import_adt_def_env(def);

        // Now, WF-check the definition.
        match *def.r(s).kind {
            AdtKind::Struct(kind) => {
                self.visit_adt_ctor(
                    &mut ccx,
                    env.self_ty,
                    &env.sig_generic_substs,
                    *kind.r(s).ctor,
                );
            }
            AdtKind::Enum(kind) => {
                for variant in kind.r(s).variants.iter() {
                    self.visit_adt_ctor(
                        &mut ccx,
                        env.self_ty,
                        &env.sig_generic_substs,
                        *variant.r(s).ctor,
                    );
                }
            }
        }
    }

    fn visit_adt_ctor(
        &mut self,
        ccx: &mut ClauseCx,
        self_ty: Ty,
        sig_generic_substs: &[GenericSubst],
        ctor: Obj<AdtCtor>,
    ) {
        let s = self.session();

        for field in ctor.r(s).fields.iter() {
            let field_ty = ccx
                .importer(self_ty, sig_generic_substs)
                .fold_spanned_ty(*field.ty);

            ccx.wf_visitor().visit_spanned(field_ty);
        }
    }

    pub fn visit_fn_item(&mut self, def: Obj<FuncItem>) {
        let s = self.session();

        self.visit_fn_def(*def.r(s).def);
    }

    pub fn visit_generic_binder(
        &mut self,
        ccx: &mut ClauseCx,
        self_ty: Ty,
        sig_generic_substs: &[GenericSubst],
        generics: Obj<GenericBinder>,
    ) {
        let s = self.session();

        for &generic in &generics.r(s).defs {
            let clauses = match generic {
                AnyGeneric::Re(generic) => *generic.r(s).clauses,
                AnyGeneric::Ty(generic) => *generic.r(s).clauses,
            };

            let clauses = ccx
                .importer(self_ty, &sig_generic_substs)
                .fold_spanned_clause_list(clauses);

            ccx.wf_visitor().visit_spanned(clauses);
        }
    }
}
