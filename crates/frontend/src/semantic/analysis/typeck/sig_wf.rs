use crate::{
    base::{
        Diag,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    semantic::{
        analysis::{
            BinderSubstitution, InferCx, InferCxMode, SubstitutionFolder, TyCtxt,
            TyFolderInfalliblePreservesSpans as _, TyVisitor, TyVisitorWalk,
        },
        syntax::{
            AnyGeneric, ImplDef, SpannedAdtInstance, SpannedTraitClauseList, SpannedTraitInstance,
            SpannedTraitParamView, SpannedTraitSpec, SpannedTy, SpannedTyOrReView, TraitClause,
            TraitDef, TraitParam, TraitSpec, TyKind, TypeGeneric,
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
        // TODO: Bind a self-type.
        self.walk_trait(def)?;

        ControlFlow::Continue(())
    }

    // FIXME: Use the new solving model
    fn visit_spanned_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        let tcx = self.tcx();
        let s = self.session();

        let generics = &spec.value.def.r(s).generics.r(s).defs;

        for (&def, param) in generics.iter().zip(spec.view(tcx).params.iter(s)) {
            match param.view(tcx) {
                SpannedTraitParamView::Equals(param) => match (def, param.view(tcx)) {
                    (AnyGeneric::Re(def), SpannedTyOrReView::Re(param)) => {
                        // TODO
                    }
                    (AnyGeneric::Ty(def), SpannedTyOrReView::Ty(param)) => {
                        if let Err(err) = InferCx::new(self.tcx(), InferCxMode::RegionAware)
                            .relate_ty_and_clause(param, *def.r(s).user_clauses)
                        {
                            Diag::span_err(
                                param.own_span().unwrap_or(Span::DUMMY),
                                "malformed parameter for trait parameter",
                            )
                            .emit();
                        }
                    }
                    _ => unreachable!(),
                },
                SpannedTraitParamView::Unspecified(_) => {
                    // (these are always fine)
                }
            }
        }

        self.walk_trait_spec(spec)?;

        ControlFlow::Continue(())
    }

    fn visit_spanned_trait_instance(
        &mut self,
        instance_orig: SpannedTraitInstance,
    ) -> ControlFlow<Self::Break> {
        let tcx = self.tcx();
        let s = self.session();

        let instance = instance_orig.view(tcx);

        // Ensure they meet their trait definition requirements.
        let trait_generic_subst = BinderSubstitution {
            binder: instance.def.r(s).generics,
            substs: instance.params.value,
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
                        def: instance.def,
                        params: tcx.intern_trait_param_list(
                            &instance
                                .params
                                .value
                                .r(s)
                                .iter()
                                .map(|&v| TraitParam::Equals(v))
                                .collect::<Vec<_>>(),
                        ),
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

        for (actual, requirements) in instance
            .params
            .iter(s)
            .zip(&instance.def.r(s).generics.r(s).defs)
        {
            let actual = actual_subst.fold_spanned_ty_or_re(actual);

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

        self.walk_trait_instance(instance_orig)?;

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
