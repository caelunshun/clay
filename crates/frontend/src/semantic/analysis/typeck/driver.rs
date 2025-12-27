use crate::{
    base::{
        Session,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    semantic::{
        analysis::{
            ClauseCx, CoherenceMap, SubstitutionFolder, TyCtxt,
            TyFolderInfalliblePreservesSpans as _, TyVisitorInfallibleExt, UnifyCxMode,
        },
        syntax::{
            AdtCtor, AdtInstance, AdtItem, AdtKind, AnyGeneric, Crate, FuncItem, GenericBinder,
            ImplItem, ItemKind, SpannedTraitClauseList, TraitClause, TraitInstance, TraitItem, Ty,
            TyKind, TypeGeneric,
        },
    },
    symbol,
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

        // Construct a `Self` type universally quantifying all possible target types on which this
        // trait could be implemented.
        let new_self_ty_generic = Obj::new(
            TypeGeneric {
                span: Span::DUMMY,
                ident: Ident {
                    span: Span::DUMMY,
                    text: symbol!("Self"),
                    raw: false,
                },
                binder: LateInit::new(None),
                user_clauses: LateInit::uninit(),
                elaborated_clauses: LateInit::uninit(),
                is_synthetic: true,
            },
            s,
        );

        let new_self_ty = tcx.intern_ty(TyKind::Universal(new_self_ty_generic));

        let mut new_self_ty_subst = SubstitutionFolder {
            tcx,
            self_ty: new_self_ty,
            substitution: None,
        };

        // Our trait has a set of input generic parameters which could refer to `Self`. Redefine
        // universals for each parameter which properly refer to the `Self` we constructed above.
        let new_self_arg_binder = tcx
            .substitute_generic_binder_clauses(def.r(s).generics, |clauses| {
                new_self_ty_subst.fold_spanned_clause_list(clauses)
            });

        let new_self_arg_spec = tcx.convert_trait_instance_to_spec(TraitInstance {
            def,
            params: tcx.convert_generic_binder_into_instance_args(new_self_arg_binder),
        });

        LateInit::init(
            &new_self_ty_generic.r(s).user_clauses,
            SpannedTraitClauseList::new_unspanned(
                tcx.intern_trait_clause_list(&[TraitClause::Trait(new_self_arg_spec)]),
            ),
        );

        // Now, we can validate our trait body.
        let TraitItem {
            item: _,
            generics: _, // (visited using `new_self_ty_params`)
            inherits,
            regular_generic_count: _,
            associated_types: _,
            methods,
        } = def.r(s);

        // First, let's ensure that the inherited trait list is well-formed.
        {
            let mut ccx = ClauseCx::new(self.tcx(), self.coherence, UnifyCxMode::RegionAware);

            let inherits = ccx
                .instantiator(new_self_ty)
                .fold_spanned_clause_list(**inherits);

            ccx.wf_visitor()
                .with_clause_applies_to(new_self_ty)
                .visit_spanned(inherits);
        }

        // Now, let's ensure that each generic parameter's clauses are well-formed.
        self.visit_generic_binder(new_self_ty, new_self_arg_binder);

        // Finally, let's check method signatures and, if a default one is provided, bodies.
        // TODO
        // for method in methods.iter() {
        //     self.visit_fn_def(method.r(s).func)?;
        // }
    }

    pub fn visit_impl(&mut self, item: Obj<ImplItem>) {
        let s = self.session();

        // `Self` lexically refers to the target type quantified by some lexical set of universal
        // generic parameters.
        let ImplItem {
            item: _,
            generics,
            trait_,
            target,
            methods,
            optimal_solve_order: _,
        } = item.r(s);

        let self_ty = item.r(s).target.value;

        // Let's ensure that the target trait instance is well formed.
        if let Some(trait_) = *trait_ {
            let mut ccx = ClauseCx::new(self.tcx(), self.coherence, UnifyCxMode::RegionAware);

            let trait_ = ccx
                .instantiator(self_ty)
                .fold_spanned_trait_instance(trait_);

            ccx.wf_visitor()
                .with_clause_applies_to(item.r(s).target.value)
                .visit_spanned(trait_);
        }

        // Let's also ensure that our target type is well-formed.
        {
            let mut ccx = ClauseCx::new(self.tcx(), self.coherence, UnifyCxMode::RegionAware);

            let target = ccx.instantiator(self_ty).fold_spanned_ty(*target);

            ccx.wf_visitor().visit_spanned(target);
        }

        // Let's ensure that `impl` generics all have well-formed clauses.
        self.visit_generic_binder(self_ty, *generics);

        // Finally, let's check method signatures and bodies.
        // TODO
        // for method in methods.iter() {
        //     self.visit_fn_def(*method)?;
        // }
    }

    pub fn visit_adt(&mut self, def: Obj<AdtItem>) {
        let s = self.session();
        let tcx = self.tcx();

        // `Self` refers to the current ADT constructed with its own generic types. Our original
        // generics may have mentioned `Self` by type so we need to construct a new set of generics
        // which are fully explicit.
        let new_binder = self
            .tcx
            .clone_generic_binder_without_clauses(def.r(s).generics);

        let new_self_ty = tcx.intern_ty(TyKind::Adt(AdtInstance {
            def,
            params: tcx.convert_generic_binder_into_instance_args(new_binder),
        }));

        let mut new_self_ty_subst = SubstitutionFolder {
            tcx,
            self_ty: new_self_ty,
            substitution: None,
        };

        tcx.init_generic_binder_clauses_of_duplicate(def.r(s).generics, new_binder, |clauses| {
            new_self_ty_subst.fold_spanned_clause_list(clauses)
        });

        // Now, WF-check the definition.
        match *def.r(s).kind {
            AdtKind::Struct(kind) => {
                self.visit_adt_ctor(new_self_ty, *kind.r(s).ctor);
            }
            AdtKind::Enum(kind) => {
                for variant in kind.r(s).variants.iter() {
                    self.visit_adt_ctor(new_self_ty, *variant.r(s).ctor);
                }
            }
        }
    }

    pub fn visit_adt_ctor(&mut self, self_ty: Ty, ctor: Obj<AdtCtor>) {
        let s = self.session();

        for field in ctor.r(s).fields.iter() {
            let mut ccx = ClauseCx::new(self.tcx(), self.coherence, UnifyCxMode::RegionAware);

            let field_ty = ccx.instantiator(self_ty).fold_spanned_ty(*field.ty);

            ccx.wf_visitor().visit_spanned(field_ty);
        }
    }

    pub fn visit_fn_item(&mut self, def: Obj<FuncItem>) {
        let s = self.session();

        self.visit_fn_def(*def.r(s).def);
    }

    pub fn visit_generic_binder(&mut self, self_ty: Ty, generics: Obj<GenericBinder>) {
        let s = self.session();
        let tcx = self.tcx();

        for &generic in &generics.r(s).defs {
            match generic {
                AnyGeneric::Re(generic) => {
                    let mut ccx = ClauseCx::new(self.tcx, self.coherence, UnifyCxMode::RegionAware);

                    let clauses = ccx
                        .instantiator(self_ty)
                        .fold_spanned_clause_list(*generic.r(s).clauses);

                    ccx.wf_visitor().visit_spanned(clauses);
                }
                AnyGeneric::Ty(generic) => {
                    let mut ccx = ClauseCx::new(self.tcx, self.coherence, UnifyCxMode::RegionAware);

                    let user_clauses = ccx
                        .instantiator(self_ty)
                        .fold_spanned_clause_list(*generic.r(s).user_clauses);

                    ccx.wf_visitor()
                        .with_clause_applies_to(tcx.intern_ty(TyKind::Universal(generic)))
                        .visit_spanned(user_clauses);
                }
            }
        }
    }
}
