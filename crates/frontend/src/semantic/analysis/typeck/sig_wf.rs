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
            AnyGeneric, ImplDef, Re, RegionGeneric, SpannedAdtInstance, SpannedTraitClauseList,
            SpannedTraitInstance, SpannedTraitParamView, SpannedTraitSpec, SpannedTy,
            SpannedTyOrRe, SpannedTyOrReView, TraitClause, TraitDef, TraitParam, TraitSpec, TyKind,
            TyOrRe, TypeGeneric,
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

        let new_self_ty_generic = Obj::new(
            // TODO: better names
            TypeGeneric {
                span: Span::DUMMY,
                ident: Ident {
                    span: Span::DUMMY,
                    text: symbol!("SelfHelper"),
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

        let new_self_ty_params = def
            .r(s)
            .generics
            .r(s)
            .defs
            .iter()
            .map(|&def| match def {
                AnyGeneric::Re(generic) => {
                    let generic = Obj::new(
                        RegionGeneric {
                            span: generic.r(s).span,
                            lifetime: generic.r(s).lifetime,
                            binder: LateInit::new(None),
                            clauses: LateInit::new(
                                new_self_ty_subst.fold_spanned_clause_list(*generic.r(s).clauses),
                            ),
                            is_synthetic: true,
                        },
                        s,
                    );

                    TraitParam::Equals(TyOrRe::Re(Re::Universal(generic)))
                }
                AnyGeneric::Ty(generic) => {
                    let generic = Obj::new(
                        TypeGeneric {
                            span: generic.r(s).span,
                            ident: generic.r(s).ident,
                            binder: LateInit::new(None),
                            user_clauses: LateInit::new(
                                new_self_ty_subst
                                    .fold_spanned_clause_list(*generic.r(s).user_clauses),
                            ),
                            elaborated_clauses: LateInit::uninit(),
                            is_synthetic: true,
                        },
                        s,
                    );

                    TraitParam::Equals(TyOrRe::Ty(tcx.intern_ty(TyKind::Universal(generic))))
                }
            })
            .collect::<Vec<_>>();

        LateInit::init(
            &new_self_ty_generic.r(s).user_clauses,
            SpannedTraitClauseList::new_unspanned(tcx.intern_trait_clause_list(&[
                TraitClause::Trait(TraitSpec {
                    def,
                    params: tcx.intern_trait_param_list(&new_self_ty_params),
                }),
            ])),
        );

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
    fn check_trait_helper(&mut self, def: Obj<TraitDef>, params: &[SpannedTyOrRe]) {
        let tcx = self.tcx();
        let s = self.session();

        // Replace `Self` for the bound `self_ty` in the input `params`.
        let mut input_subst = SubstitutionFolder {
            tcx,
            self_ty: self.self_ty.unwrap().value,
            substitution: None,
        };

        let params = params
            .iter()
            .map(|&v| input_subst.fold_spanned_ty_or_re(v))
            .collect::<Vec<_>>();

        let params = &params;

        // Create a folder to replace generics in the trait with the user's supplied generics.
        let mut trait_subst = SubstitutionFolder {
            tcx,
            self_ty: self.self_ty.unwrap().value,
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

                    if let Err(err) = InferCx::new(tcx, InferCxMode::RegionAware)
                        .relate_ty_and_clause(actual, requirements)
                    {
                        Diag::span_err(
                            actual.own_span().unwrap(),
                            "malformed parameter for trait parameter",
                        )
                        .emit();

                        dbg!(err);
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}
