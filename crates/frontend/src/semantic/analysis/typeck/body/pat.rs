use crate::{
    base::arena::{HasInterner as _, Obj},
    parse::ast::AstMutability,
    semantic::{
        analysis::{BodyCtxt, ClauseOrigin, ClauseOriginKind, HrtbUniverse},
        syntax::{
            Divergence, HirPat, HirPatKind, InferTyVarSourceInfo, Mutability, Re, RelationMode, Ty,
            TyKind,
        },
    },
};

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn check_pat_infer(&mut self, pat: Obj<HirPat>, divergence: Option<&mut Divergence>) -> Ty {
        let s = self.session();
        let infer = self.ccx_mut().fresh_ty_infer(
            HrtbUniverse::ROOT,
            InferTyVarSourceInfo::PatType {
                span: pat.r(s).span,
            },
        );

        self.check_pat_demand(pat, infer, divergence);
        infer
    }

    pub fn check_pat_demand(
        &mut self,
        pat: Obj<HirPat>,
        demand: Ty,
        divergence: Option<&mut Divergence>,
    ) {
        self.check_pat_inner(pat, demand, None, divergence)
    }

    fn check_pat_inner(
        &mut self,
        pat: Obj<HirPat>,
        demand: Ty,
        default_by_ref: Option<Mutability>,
        mut divergence: Option<&mut Divergence>,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        match pat.r(s).kind {
            HirPatKind::Hole | HirPatKind::Error(_) => {
                // (trivially allowed)
            }
            HirPatKind::Binding(by_ref, name, binding) => {
                let by_ref = by_ref
                    .as_explicit()
                    .map(AstMutability::strip_span)
                    .or(default_by_ref);

                let local_ty = self.type_of_local(name);
                let bound_ty = if let Some(by_ref) = by_ref {
                    tcx.intern(TyKind::Reference(Re::Erased, by_ref, demand))
                } else {
                    demand
                };

                self.ccx_mut().oblige_ty_unifies_ty(
                    ClauseOrigin::root_report(ClauseOriginKind::Pattern {
                        pat_span: pat.r(s).span,
                    }),
                    local_ty,
                    bound_ty,
                    RelationMode::Equate,
                );

                if let Some(binding) = binding {
                    self.check_pat_inner(binding, demand, default_by_ref, divergence);
                }
            }
            HirPatKind::Slice(hir_pat_list_front_and_tail) => todo!(),
            HirPatKind::Tuple(params) => todo!(),
            HirPatKind::Lit(obj) => todo!(),
            HirPatKind::Or(patterns) => {
                for &pat in patterns.r(s) {
                    self.check_pat_inner(pat, demand, default_by_ref, divergence.as_deref_mut());
                }
            }
            HirPatKind::Deref(mutability, obj) => todo!(),
            HirPatKind::AdtUnit(adt_ctor_instance) => todo!(),
            HirPatKind::AdtTuple(adt_ctor_instance, hir_pat_list_front_and_tail) => todo!(),
            HirPatKind::AdtNamed(adt_ctor_instance, obj) => todo!(),
            HirPatKind::PlaceExpr(place) => {
                self.check_expr_demand(place, demand)
                    .and_do(divergence.unwrap());
            }
            HirPatKind::Range(hir_range_expr) => todo!(),
        }
    }

    fn peel_references_for_pat(
        &mut self,
        demand: &mut Ty,
        default_by_ref: &mut Option<Mutability>,
    ) {
        let s = self.session();

        loop {
            *demand = self.ccx_mut().peel_ty_infer_var_after_poll(*demand);

            let TyKind::Reference(_re, muta, pointee) = *demand.r(s) else {
                break;
            };

            *default_by_ref = Some((default_by_ref.unwrap_or(muta)).min(muta));
            *demand = pointee;
        }
    }
}
