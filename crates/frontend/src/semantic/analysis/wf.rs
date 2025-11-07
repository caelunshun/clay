use crate::{
    base::{Diag, arena::Obj, syntax::Span},
    semantic::{
        analysis::{InferVarInferences, TyCtxt, TyVisitor, TyVisitorWalk},
        syntax::{
            AnyGeneric, Crate, GenericBinder, ImplDef, SpannedAdtInstance, SpannedTraitInstance,
            SpannedTraitSpec, TraitParam, TyOrRe,
        },
    },
};
use std::{convert::Infallible, ops::ControlFlow};

impl TyCtxt {
    pub fn wf_check_crate(&self, krate: Obj<Crate>) {
        let s = &self.session;

        for &impl_ in &**krate.r(s).impls {
            self.determine_impl_generic_solve_order(impl_);
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

    // === WF checks === //

    fn visit_impl(&mut self, item: Obj<ImplDef>) -> ControlFlow<Self::Break> {
        // TODO: Check super-traits

        self.walk_impl(item)?;

        ControlFlow::Continue(())
    }

    fn visit_spanned_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        let tcx = self.tcx();
        let s = &self.session();

        let generics = &spec.value.def.r(s).generics.r(s).generics;

        for (&def, &param) in generics.iter().zip(spec.value.params.r(s)) {
            match param {
                TraitParam::Equals(param) => match (def, param) {
                    (AnyGeneric::Re(def), TyOrRe::Re(param)) => {
                        // TODO
                    }
                    (AnyGeneric::Ty(def), TyOrRe::Ty(param)) => {
                        let mut binder = GenericBinder::default();

                        let mut failures = Vec::new();

                        tcx.check_clause_list_assignability_erase_regions(
                            param,
                            def.r(s).user_clauses.value,
                            &mut binder,
                            &mut InferVarInferences::default(),
                            &mut failures,
                        );

                        if !failures.is_empty() {
                            Diag::span_err(
                                spec.own_span().unwrap_or(Span::DUMMY),
                                "malformed parameters for trait clause",
                            )
                            .emit();
                        }
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(_) => {
                    // (these are always fine)
                }
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_spanned_trait_instance(
        &mut self,
        instance: SpannedTraitInstance,
    ) -> ControlFlow<Self::Break> {
        // TODO

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
