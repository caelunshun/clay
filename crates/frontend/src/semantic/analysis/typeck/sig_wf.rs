use crate::{
    base::{
        Diag,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    semantic::{
        analysis::{
            BinderSubstitution, ExplicitInferVisitor, InferCx, InferCxMode, SubstitutionFolder,
            TyCtxt, TyFolderInfalliblePreservesSpans as _, TyVisitor, TyVisitorUnspanned,
            TyVisitorWalk,
        },
        syntax::{
            AnyGeneric, ImplDef, Re, SpannedAdtInstance, SpannedTraitClauseList,
            SpannedTraitInstance, SpannedTraitParamView, SpannedTraitSpec, SpannedTy,
            SpannedTyOrRe, SpannedTyOrReView, TraitClause, TraitDef, TraitParam, TraitParamList,
            TraitSpec, TyKind, TyOrRe, TypeGeneric,
        },
    },
    symbol,
};
use std::{convert::Infallible, ops::ControlFlow};

#[derive(Debug, Clone)]
pub struct SignatureWfVisitor<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub self_ty: Option<SpannedTy>,
}

impl<'tcx> TyVisitor<'tcx> for SignatureWfVisitor<'tcx> {
    type Break = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    fn visit_impl(&mut self, item: Obj<ImplDef>) -> ControlFlow<Self::Break> {
        let s = self.session();

        // TODO: Check super-traits

        let old_self_ty = self.self_ty.replace(item.r(s).target);
        self.walk_impl(item)?;
        self.self_ty = old_self_ty;

        ControlFlow::Continue(())
    }

    fn visit_trait(&mut self, def: Obj<TraitDef>) -> ControlFlow<Self::Break> {
        let tcx = self.tcx();
        let s = self.session();

        let new_self_ty_params = def
            .r(s)
            .generics
            .r(s)
            .defs
            .iter()
            .map(|&def| match def {
                AnyGeneric::Re(generic) => TraitParam::Equals(TyOrRe::Re(Re::Universal(generic))),
                AnyGeneric::Ty(generic) => {
                    TraitParam::Equals(TyOrRe::Ty(tcx.intern_ty(TyKind::Universal(generic))))
                }
            })
            .collect::<Vec<_>>();

        let new_self_ty_params = tcx.intern_trait_param_list(&new_self_ty_params);

        let new_self_ty = Obj::new(
            // TODO: better names
            TypeGeneric {
                span: Span::DUMMY,
                ident: Ident {
                    span: Span::DUMMY,
                    text: symbol!("SelfHelper"),
                    raw: false,
                },
                binder: LateInit::uninit(),
                user_clauses: LateInit::new(SpannedTraitClauseList::new_unspanned(
                    tcx.intern_trait_clause_list(&[TraitClause::Trait(TraitSpec {
                        def,
                        params: new_self_ty_params,
                    })]),
                )),
                elaborated_clauses: LateInit::uninit(),
                is_synthetic: true,
            },
            s,
        );

        let new_self_ty = tcx.intern_ty(TyKind::Universal(new_self_ty));

        let old_self_ty = self.self_ty.replace(SpannedTy::new_saturated(
            new_self_ty,
            def.r(s).item.r(s).name.span,
            s,
        ));
        self.walk_trait(def)?;
        self.self_ty = old_self_ty;

        ControlFlow::Continue(())
    }

    fn visit_spanned_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        let tcx = self.tcx();
        let s = self.session();

        self.check_trait_helper(
            spec.value.def,
            &spec
                .view(tcx)
                .params
                .iter(s)
                .map(|param| match param.view(tcx) {
                    SpannedTraitParamView::Equals(v) => v,
                    SpannedTraitParamView::Unspecified(_) => SpannedTyOrRe::new_unspanned(
                        TyOrRe::Ty(tcx.intern_ty(TyKind::ExplicitInfer)),
                    ),
                })
                .collect::<Vec<_>>(),
            spec.value.params,
        );

        self.walk_trait_spec(spec)?;

        ControlFlow::Continue(())
    }

    fn visit_spanned_trait_instance(
        &mut self,
        instance: SpannedTraitInstance,
    ) -> ControlFlow<Self::Break> {
        let tcx = self.tcx();
        let s = self.session();

        self.check_trait_helper(
            instance.value.def,
            &instance.view(tcx).params.iter(s).collect::<Vec<_>>(),
            tcx.intern_trait_param_list(
                &instance
                    .value
                    .params
                    .r(s)
                    .iter()
                    .map(|&v| TraitParam::Equals(v))
                    .collect::<Vec<_>>(),
            ),
        );

        self.walk_trait_instance(instance)?;

        ControlFlow::Continue(())
    }

    fn visit_spanned_adt_instance(
        &mut self,
        instance: SpannedAdtInstance,
    ) -> ControlFlow<Self::Break> {
        // TODO

        ControlFlow::Continue(())
    }
}

impl SignatureWfVisitor<'_> {
    fn check_trait_helper(
        &mut self,
        def: Obj<TraitDef>,
        params_as_tys: &[SpannedTyOrRe],
        params_as_params: TraitParamList,
    ) {
        let tcx = self.tcx();
        let s = self.session();

        let trait_generic_subst = BinderSubstitution {
            binder: def.r(s).generics,
            substs: tcx
                .intern_ty_or_re_list(&params_as_tys.iter().map(|v| v.value).collect::<Vec<_>>()),
        };

        let trait_self_subst = Obj::new(
            // TODO: better names
            TypeGeneric {
                span: Span::DUMMY,
                ident: Ident {
                    span: Span::DUMMY,
                    text: symbol!("SelfHelper"),
                    raw: false,
                },
                binder: LateInit::uninit(),
                user_clauses: LateInit::new(SpannedTraitClauseList::new_unspanned(
                    tcx.intern_trait_clause_list(&[TraitClause::Trait(TraitSpec {
                        def,
                        params: params_as_params,
                    })]),
                )),
                elaborated_clauses: LateInit::uninit(),
                is_synthetic: true,
            },
            s,
        );

        let trait_self_subst = tcx.intern_ty(TyKind::Universal(trait_self_subst));

        let mut actual_subst = SubstitutionFolder {
            tcx,
            self_ty: self.self_ty.unwrap().value,
            substitution: None,
        };

        let mut trait_subst = SubstitutionFolder {
            tcx,
            self_ty: trait_self_subst,
            substitution: Some(trait_generic_subst),
        };

        for (&actual, requirements) in params_as_tys.iter().zip(&def.r(s).generics.r(s).defs) {
            let actual = actual_subst.fold_spanned_ty_or_re(actual);

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

                    InferCx::new(tcx, InferCxMode::RegionAware)
                        .relate_re_and_clause(actual, requirements);
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

                    if let Err(_err) = InferCx::new(tcx, InferCxMode::RegionAware)
                        .relate_ty_and_clause(actual, requirements)
                    {
                        Diag::span_err(
                            actual.own_span().unwrap(),
                            "malformed parameter for trait parameter",
                        )
                        .emit();
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}
