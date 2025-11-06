use crate::{
    base::{Diag, arena::Obj, syntax::Span},
    typeck::{
        analysis::{InferVarInferences, TyCtxt},
        syntax::{
            AnyGeneric, Crate, GenericBinder, ImplDef, Item, TraitClause, TraitClauseList,
            TraitParam, TraitSpec, Ty, TyOrRe,
        },
    },
};

impl TyCtxt {
    pub fn wf_check_crate(&self, krate: Obj<Crate>) {
        let s = &self.session;

        for &impl_ in &**krate.r(s).impls {
            self.determine_impl_generic_solve_order(impl_);
        }

        for &item in &**krate.r(s).items {
            self.wf_check_item(item);
        }

        for &impl_ in &**krate.r(s).impls {
            self.wf_check_impl(impl_);
        }
    }

    pub fn wf_check_item(&self, item: Obj<Item>) {
        let s = &self.session;

        // TODO
    }

    pub fn wf_check_impl(&self, impl_: Obj<ImplDef>) {
        let s = &self.session;

        self.wf_check_binder(impl_.r(s).generics);
    }

    pub fn wf_check_binder(&self, binder: Obj<GenericBinder>) {
        let s = &self.session;

        for &generic in &binder.r(s).generics {
            self.wf_check_generic(generic);
        }
    }

    pub fn wf_check_generic(&self, generic: AnyGeneric) {
        let s = &self.session;

        match generic {
            AnyGeneric::Re(generic) => {
                self.wf_check_clauses(*generic.r(s).clauses);
            }
            AnyGeneric::Ty(generic) => {
                self.wf_check_clauses(*generic.r(s).user_clauses);
            }
        }
    }

    pub fn wf_check_clauses(&self, clauses: TraitClauseList) {
        for &clause in clauses.r(&self.session) {
            self.wf_check_clause(clause);
        }
    }

    pub fn wf_check_clause(&self, clause: TraitClause) {
        match clause {
            TraitClause::Outlives(re) => {
                // TODO
            }
            TraitClause::Trait(spec) => {
                self.wf_check_trait_spec(Span::DUMMY, spec);
            }
        }
    }

    pub fn wf_check_trait_spec(&self, span: Span, spec: TraitSpec) {
        let s = &self.session;

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

                        self.check_clause_list_assignability_erase_regions(
                            param,
                            *def.r(s).user_clauses,
                            &mut binder,
                            &mut InferVarInferences::default(),
                            &mut failures,
                        );

                        if !failures.is_empty() {
                            Diag::span_err(span, "malformed >:3").emit();
                        }
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(_) => {
                    // (these are always fine)
                }
            }
        }
    }

    pub fn wf_check_ty_self_satisfies(&self, ty: Ty) {
        // TODO
    }
}
