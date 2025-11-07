use crate::{
    base::{Diag, arena::Obj, syntax::Span},
    semantic::{
        analysis::{InferVarInferences, TyCtxt, TyVisitor, TyVisitorWalk},
        syntax::{
            AdtInstance, AnyGeneric, Crate, GenericBinder, ImplDef, Item, TraitInstance,
            TraitParam, TraitSpec, TyOrRe,
        },
    },
};
use std::{convert::Infallible, mem, ops::ControlFlow};

impl TyCtxt {
    pub fn wf_check_crate(&self, krate: Obj<Crate>) {
        let s = &self.session;

        for &impl_ in &**krate.r(s).impls {
            self.determine_impl_generic_solve_order(impl_);
        }

        _ = SignatureWfVisitor {
            tcx: self,
            ctx_span: Span::DUMMY,
        }
        .visit_crate(krate);
    }
}

#[derive(Debug, Clone)]
pub struct SignatureWfVisitor<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub ctx_span: Span,
}

impl SignatureWfVisitor<'_> {
    pub fn wrap_cx<R>(&mut self, sp: Span, f: impl FnOnce(&mut Self) -> R) -> R {
        let old = mem::replace(&mut self.ctx_span, sp);
        let res = f(self);
        self.ctx_span = old;
        res
    }
}

impl<'tcx> TyVisitor<'tcx> for SignatureWfVisitor<'tcx> {
    type Break = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    // === Span annotators === //

    fn visit_item(&mut self, item: Obj<Item>) -> ControlFlow<Self::Break> {
        self.wrap_cx(item.r(self.session()).name.span, |this| {
            this.walk_item(item)
        })?;

        ControlFlow::Continue(())
    }

    fn visit_any_generic_def(&mut self, generic: AnyGeneric) -> ControlFlow<Self::Break> {
        self.wrap_cx(generic.span(self.session()), |this| {
            this.walk_any_generic_def(generic)
        })?;

        ControlFlow::Continue(())
    }

    // === WF checks === //

    fn visit_impl(&mut self, item: Obj<ImplDef>) -> ControlFlow<Self::Break> {
        self.wrap_cx(item.r(self.session()).span.truncate_left(4), |this| {
            this.walk_impl(item)
        })?;

        // TODO: Check super-traits

        ControlFlow::Continue(())
    }

    fn visit_trait_spec(&mut self, spec: TraitSpec) -> ControlFlow<Self::Break> {
        let tcx = self.tcx();
        let s = &self.session();

        let generics = &spec.def.r(s).generics.r(s).generics;

        for (&def, &param) in generics.iter().zip(spec.params.r(s)) {
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
                            *def.r(s).user_clauses,
                            &mut binder,
                            &mut InferVarInferences::default(),
                            &mut failures,
                        );

                        if !failures.is_empty() {
                            Diag::span_err(self.ctx_span, "malformed parameters for trait clause")
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

    fn visit_trait_instance(&mut self, instance: TraitInstance) -> ControlFlow<Self::Break> {
        // TODO

        ControlFlow::Continue(())
    }

    fn visit_adt_instance(&mut self, instance: AdtInstance) -> ControlFlow<Self::Break> {
        // TODO

        ControlFlow::Continue(())
    }
}
