use crate::{
    base::{
        Diag,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    semantic::{
        analysis::{
            BinderSubstitution, CoherenceMap, ExplicitInferVisitor, SubstitutionFolder, TyCtxt,
            TyFolderInfalliblePreservesSpans as _, TyVisitor, TyVisitorUnspanned, TyVisitorWalk,
            UnifyCx, UnifyCxMode,
        },
        syntax::{
            AdtCtor, AdtInstance, AdtItem, AdtKind, AnyGeneric, Crate, FuncItem, GenericBinder,
            ImplItem, ItemKind, SpannedAdtInstance, SpannedTraitClauseList, SpannedTraitInstance,
            SpannedTraitParamView, SpannedTraitSpec, SpannedTy, SpannedTyOrRe, SpannedTyOrReList,
            SpannedTyOrReView, SpannedTyView, TraitClause, TraitInstance, TraitItem, Ty, TyKind,
            TyOrRe, TypeGeneric,
        },
    },
    symbol,
};
use std::{convert::Infallible, ops::ControlFlow};

#[derive(Debug, Clone)]
pub struct CrateTypeckVisitor<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub coherence: &'tcx CoherenceMap,
    pub self_ty: Option<Ty>,
    pub clause_applies_to: Option<Ty>,
}

impl CrateTypeckVisitor<'_> {
    pub fn visit_crate(&mut self, krate: Obj<Crate>) -> ControlFlow<Infallible> {
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
                    self.visit_adt(def)?;
                }
                ItemKind::EnumVariant(_) => {
                    // (already visited in ADT checks)
                }
                ItemKind::Trait(def) => {
                    self.visit_trait(def)?;
                }
                ItemKind::Impl(def) => {
                    self.visit_impl(def)?;
                }
                ItemKind::Func(def) => {
                    self.visit_fn_item(def)?;
                }
            }
        }

        ControlFlow::Continue(())
    }

    pub fn visit_trait(&mut self, def: Obj<TraitItem>) -> ControlFlow<Infallible> {
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
        let old_self_ty = self.self_ty.replace(new_self_ty);
        {
            let TraitItem {
                item: _,
                generics: _, // (visited using `new_self_ty_params`)
                inherits,
                regular_generic_count: _,
                associated_types: _,
                methods,
            } = def.r(s);

            // First, let's ensure that the inherited trait list is well-formed.
            let old_clause_applies_to = self.clause_applies_to.replace(new_self_ty);
            self.visit_spanned_clause_list(**inherits)?;
            self.clause_applies_to = old_clause_applies_to;

            // Now, let's ensure that each generic parameter's clauses are well-formed.
            self.visit_generic_binder(new_self_arg_binder)?;

            // Finally, let's check method signatures and, if a default one is provided, bodies.
            // TODO
            // for method in methods.iter() {
            //     self.visit_fn_def(method.r(s).func)?;
            // }
        }
        self.self_ty = old_self_ty;

        ControlFlow::Continue(())
    }

    pub fn visit_impl(&mut self, item: Obj<ImplItem>) -> ControlFlow<Infallible> {
        let s = self.session();

        // `Self` lexically refers to the target type quantified by some lexical set of universal
        // generic parameters.
        let old_self_ty = self.self_ty.replace(item.r(s).target.value);
        {
            let ImplItem {
                item: _,
                generics,
                trait_,
                target,
                methods,
                generic_solve_order: _,
            } = item.r(s);

            // Let's ensure that the target trait instance is well formed.
            if let Some(trait_) = *trait_ {
                let old_clause_applies_to = self.clause_applies_to.replace(item.r(s).target.value);
                self.visit_spanned_trait_instance(trait_)?;
                self.clause_applies_to = old_clause_applies_to;
            }

            // Let's also ensure that our target type is well-formed.
            self.visit_spanned_ty(*target)?;

            // Let's ensure that `impl` generics all have well-formed clauses.
            self.visit_generic_binder(*generics)?;

            // Finally, let's check method signatures and bodies.
            // TODO
            // for method in methods.iter() {
            //     self.visit_fn_def(*method)?;
            // }
        }
        self.self_ty = old_self_ty;

        ControlFlow::Continue(())
    }

    pub fn visit_adt(&mut self, def: Obj<AdtItem>) -> ControlFlow<Infallible> {
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
        let old_self_ty = self.self_ty.replace(new_self_ty);
        {
            match *def.r(s).kind {
                AdtKind::Struct(kind) => {
                    self.visit_adt_ctor(*kind.r(s).ctor)?;
                }
                AdtKind::Enum(kind) => {
                    for variant in kind.r(s).variants.iter() {
                        self.visit_adt_ctor(*variant.r(s).ctor)?;
                    }
                }
            }
        }
        self.self_ty = old_self_ty;

        ControlFlow::Continue(())
    }

    pub fn visit_adt_ctor(&mut self, ctor: Obj<AdtCtor>) -> ControlFlow<Infallible> {
        let s = self.session();

        for field in ctor.r(s).fields.iter() {
            self.visit_spanned_ty(*field.ty)?;
        }

        ControlFlow::Continue(())
    }

    pub fn visit_fn_item(&mut self, def: Obj<FuncItem>) -> ControlFlow<Infallible> {
        let s = self.session();

        self.visit_fn_def(*def.r(s).def)?;

        ControlFlow::Continue(())
    }

    pub fn visit_generic_binder(
        &mut self,
        generics: Obj<GenericBinder>,
    ) -> ControlFlow<Infallible> {
        let s = self.session();
        let tcx = self.tcx();

        for &generic in &generics.r(s).defs {
            match generic {
                AnyGeneric::Re(generic) => {
                    self.visit_spanned_clause_list(*generic.r(s).clauses)?;
                }
                AnyGeneric::Ty(generic) => {
                    let old_clause_applies_to = self
                        .clause_applies_to
                        .replace(tcx.intern_ty(TyKind::Universal(generic)));

                    self.visit_spanned_clause_list(*generic.r(s).user_clauses)?;

                    self.clause_applies_to = old_clause_applies_to;
                }
            }
        }

        ControlFlow::Continue(())
    }
}

impl<'tcx> TyVisitor<'tcx> for CrateTypeckVisitor<'tcx> {
    type Break = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    fn visit_spanned_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
        match ty.view(self.tcx()) {
            SpannedTyView::Trait(_) => {
                let old_clause_applies_to = self.clause_applies_to.replace(ty.value);
                self.walk_ty(ty)?;
                self.clause_applies_to = old_clause_applies_to;
            }
            SpannedTyView::This
            | SpannedTyView::Simple(..)
            | SpannedTyView::Reference(..)
            | SpannedTyView::Adt(..)
            | SpannedTyView::Tuple(..)
            | SpannedTyView::FnDef(..)
            | SpannedTyView::ExplicitInfer
            | SpannedTyView::Universal(..)
            | SpannedTyView::InferVar(..)
            | SpannedTyView::Error(..) => {
                self.walk_ty(ty)?;
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_spanned_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        let tcx = self.tcx();

        let params = spec
            .view(tcx)
            .params
            .iter(tcx)
            .map(|param| match param.view(tcx) {
                SpannedTraitParamView::Equals(v) => v,
                SpannedTraitParamView::Unspecified(_) => {
                    SpannedTyOrRe::new_unspanned(TyOrRe::Ty(tcx.intern_ty(TyKind::ExplicitInfer)))
                }
            })
            .collect::<Vec<_>>();

        let params =
            SpannedTyOrReList::alloc_list(spec.own_span().unwrap_or(Span::DUMMY), &params, tcx);

        self.check_trait_helper(spec.value.def, params);

        self.walk_trait_spec(spec)?;

        ControlFlow::Continue(())
    }

    fn visit_spanned_trait_instance(
        &mut self,
        instance: SpannedTraitInstance,
    ) -> ControlFlow<Self::Break> {
        let tcx = self.tcx();

        self.check_trait_helper(instance.value.def, instance.view(tcx).params);
        self.walk_trait_instance(instance)?;

        ControlFlow::Continue(())
    }

    fn visit_spanned_adt_instance(
        &mut self,
        instance: SpannedAdtInstance,
    ) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        // TODO

        self.walk_adt_instance(instance)?;

        ControlFlow::Continue(())
    }
}

impl CrateTypeckVisitor<'_> {
    fn check_trait_helper(&mut self, def: Obj<TraitItem>, params: SpannedTyOrReList) {
        let tcx = self.tcx();
        let s = self.session();

        // Replace `Self` for the bound `self_ty` in the input `params`.
        let mut input_subst = SubstitutionFolder {
            tcx,
            self_ty: self.self_ty.unwrap_or(tcx.intern_ty(TyKind::This)),
            substitution: None,
        };

        let params = params
            .iter(tcx)
            .map(|v| input_subst.fold_spanned_ty_or_re(v))
            .collect::<Vec<_>>();

        let params = &params;

        // Create a folder to replace generics in the trait with the user's supplied generics.
        let mut trait_subst = SubstitutionFolder {
            tcx,
            self_ty: self.clause_applies_to.unwrap(),
            substitution: Some(BinderSubstitution {
                binder: def.r(s).generics,
                substs: tcx
                    .intern_ty_or_re_list(&params.iter().map(|v| v.value).collect::<Vec<_>>()),
            }),
        };

        for (&actual, requirements) in params.iter().zip(&def.r(s).generics.r(s).defs) {
            let actual = input_subst.fold_spanned_ty_or_re(actual);

            if ExplicitInferVisitor(tcx)
                .visit_ty_or_re(actual.value)
                .is_break()
            {
                continue;
            }

            match (actual.view(tcx), requirements) {
                (SpannedTyOrReView::Re(actual), AnyGeneric::Re(requirements)) => {
                    let requirements =
                        trait_subst.fold_spanned_clause_list(*requirements.r(s).clauses);

                    if let Err(err) = UnifyCx::new(tcx, self.coherence, UnifyCxMode::RegionAware)
                        .relate_re_and_clause(actual.value, requirements.value)
                    {
                        Diag::span_err(
                            actual.own_span().unwrap(),
                            "malformed parameter for trait parameter",
                        )
                        .emit();

                        // dbg!(err);
                    }
                }
                (SpannedTyOrReView::Ty(actual), AnyGeneric::Ty(requirements)) => {
                    let requirements =
                        trait_subst.fold_spanned_clause_list(*requirements.r(s).user_clauses);

                    if ExplicitInferVisitor(tcx)
                        .visit_clause_list(requirements.value)
                        .is_break()
                    {
                        continue;
                    }

                    if let Err(err) = UnifyCx::new(tcx, self.coherence, UnifyCxMode::RegionAware)
                        .relate_ty_and_clause(actual.value, requirements.value)
                    {
                        Diag::span_err(
                            actual.own_span().unwrap(),
                            "malformed parameter for trait parameter",
                        )
                        .emit();

                        // dbg!(err);
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}
