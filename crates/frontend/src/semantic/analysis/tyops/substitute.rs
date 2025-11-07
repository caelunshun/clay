use crate::{
    base::arena::Obj,
    semantic::{
        analysis::{TyCtxt, TyFolder},
        syntax::{GenericBinder, Re, RegionGeneric, Ty, TyKind, TyOrReList, TypeGeneric},
    },
};
use std::convert::Infallible;

#[derive(Debug, Copy, Clone)]
pub struct SubstitutionFolder<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub self_ty: Ty,
    pub substitution: BinderSubstitution,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct BinderSubstitution {
    pub binder: Obj<GenericBinder>,
    pub substs: TyOrReList,
}

impl<'tcx> SubstitutionFolder<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, self_ty: Ty, substitution: BinderSubstitution) -> Self {
        Self {
            tcx,
            self_ty,
            substitution,
        }
    }
}

impl<'tcx> TyFolder<'tcx> for SubstitutionFolder<'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    fn visit_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        let mapped = self
            .tcx
            .queries
            .substitute_ty
            .compute_infallible((ty, self.self_ty, self.substitution), |_| {
                self.walk_ty(ty).unwrap()
            });

        Ok(mapped)
    }

    fn visit_ty_generic_use(&mut self, generic: Obj<TypeGeneric>) -> Result<Ty, Self::Error> {
        let s = &self.tcx.session;

        let pos_in_binder = *generic.r(s).binder;

        if pos_in_binder.def != self.substitution.binder {
            return Ok(self.tcx.intern_ty(TyKind::Universal(generic)));
        }

        Ok(self.substitution.substs.r(s)[pos_in_binder.idx as usize].unwrap_ty())
    }

    fn visit_re_generic_use(&mut self, generic: Obj<RegionGeneric>) -> Result<Re, Self::Error> {
        let s = &self.tcx.session;

        let pos_in_binder = *generic.r(s).binder;

        if pos_in_binder.def != self.substitution.binder {
            return Ok(Re::Universal(generic));
        }

        Ok(self.substitution.substs.r(s)[pos_in_binder.idx as usize].unwrap_re())
    }

    fn visit_self_ty_use(&mut self) -> Result<Ty, Self::Error> {
        Ok(self.self_ty)
    }
}
