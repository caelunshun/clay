use crate::{
    base::{
        Diag,
        analysis::Spanned,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    semantic::{
        analysis::{
            BinderSubstitution, InferCx, InferCxMode, SubstitutionFolder, TyCtxt,
            TyFolderInfallible, TyVisitor, TyVisitorWalk,
        },
        syntax::{
            AnyGeneric, Crate, GenericBinder, ImplDef, SpannedAdtInstance, SpannedTraitClauseList,
            SpannedTraitInstance, SpannedTraitParamView, SpannedTraitSpec, SpannedTyOrReView,
            TraitClause, TraitParam, TraitSpec, TyKind, TypeGeneric,
        },
    },
    symbol,
};
use std::{convert::Infallible, ops::ControlFlow};

impl TyCtxt {
    pub fn wf_check_crate(&self, krate: Obj<Crate>) {
        let s = &self.session;

        for &def in &**krate.r(s).impls {
            self.determine_impl_generic_solve_order(def);
        }

        _ = SignatureWfVisitor { tcx: self }.visit_crate(krate);
    }
}

#[derive(Debug, Clone)]
pub struct SignatureWfVisitor<'tcx> {
    pub tcx: &'tcx TyCtxt,
}

impl<'tcx> TyVisitor<'tcx> for SignatureWfVisitor<'tcx> {
    type Break = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    fn visit_impl(&mut self, item: Obj<ImplDef>) -> ControlFlow<Self::Break> {
        // TODO: Check super-traits

        self.walk_impl(item)?;

        ControlFlow::Continue(())
    }

    // FIXME: Use the new solving model
    fn visit_spanned_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        let tcx = self.tcx();
        let s = self.session();

        let generics = &spec.value.def.r(s).generics.r(s).generics;

        for (&def, param) in generics.iter().zip(spec.view(tcx).params.iter(s)) {
            match param.view(tcx) {
                SpannedTraitParamView::Equals(param) => match (def, param.view(tcx)) {
                    (AnyGeneric::Re(def), SpannedTyOrReView::Re(param)) => {
                        // TODO
                    }
                    (AnyGeneric::Ty(def), SpannedTyOrReView::Ty(param)) => {
                        let mut binder = GenericBinder::default();

                        if let Err(err) = InferCx::new(self.tcx(), InferCxMode::RegionAware)
                            .relate_ty_and_clause(param, *def.r(s).user_clauses, &mut binder)
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
                user_clauses: LateInit::new(Spanned::new_unspanned(
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

        let mut trait_subst = SubstitutionFolder {
            tcx,
            self_ty: trait_self_subst,
            substitution: trait_generic_subst,
        };

        for (actual, requirements) in instance
            .params
            .iter(s)
            .zip(&instance.def.r(s).generics.r(s).generics)
        {
            match (actual.view(tcx), requirements) {
                (SpannedTyOrReView::Re(actual), AnyGeneric::Re(requirements)) => {
                    let requirements =
                        trait_subst.fold_clause_list(requirements.r(s).clauses.value);

                    InferCx::new(tcx, InferCxMode::RegionAware).relate_re_and_clause(
                        actual,
                        SpannedTraitClauseList::new_unspanned(requirements),
                    );
                }
                (SpannedTyOrReView::Ty(actual), AnyGeneric::Ty(requirements)) => {
                    let requirements =
                        trait_subst.fold_clause_list(requirements.r(s).user_clauses.value);

                    if let Err(_err) = InferCx::new(tcx, InferCxMode::RegionAware)
                        .relate_ty_and_clause(
                            actual,
                            SpannedTraitClauseList::new_unspanned(requirements),
                            &mut GenericBinder::default(),
                        )
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

    // TODO: Check outlives constraints for lifetimes
}
