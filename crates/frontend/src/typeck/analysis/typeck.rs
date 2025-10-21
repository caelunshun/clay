use crate::{
    base::arena::Obj,
    match_pair,
    typeck::{
        analysis::TyCtxt,
        syntax::{GenericInstance, Re, Ty, TyKind, TyList, TyOrRe, TyOrReList, Variance},
    },
};

impl TyCtxt {
    pub fn substitute_ty(&self, target: Ty, self_ty: Ty, generics: GenericInstance) -> Ty {
        self.queries
            .substitute_ty
            .compute((target, self_ty, generics), |_| {
                Ok(self.substitute_inner(target, self_ty, generics))
            })
            .unwrap()
    }

    pub fn substitute_ty_list(
        &self,
        target: TyList,
        self_ty: Ty,
        generics: GenericInstance,
    ) -> TyList {
        self.queries
            .substitute_ty_list
            .compute((target, self_ty, generics), |_| {
                Ok(self.intern_tys(
                    &target
                        .r(&self.session)
                        .iter()
                        .map(|&ty| self.substitute_ty(ty, self_ty, generics))
                        .collect::<Vec<_>>(),
                ))
            })
            .unwrap()
    }

    pub fn substitute_ty_or_re_list(
        &self,
        target: TyOrReList,
        self_ty: Ty,
        generics: GenericInstance,
    ) -> TyOrReList {
        self.queries
            .substitute_ty_or_re_list
            .compute((target, self_ty, generics), |_| {
                Ok(self.intern_ty_or_re_list(
                    &target
                        .r(&self.session)
                        .iter()
                        .map(|&ty_or_re| match ty_or_re {
                            TyOrRe::Ty(ty) => TyOrRe::Ty(self.substitute_ty(ty, self_ty, generics)),
                            TyOrRe::Re(re) => TyOrRe::Re(self.substitute_re(re, generics)),
                        })
                        .collect::<Vec<_>>(),
                ))
            })
            .unwrap()
    }

    pub fn substitute_re(&self, re: Re, generics: GenericInstance) -> Re {
        let s = &self.session;

        match re {
            Re::Gc | Re::Infer | Re::Erased => re,
            Re::Generic(generic) => {
                if *generic.r(s).binder == generics.binder {
                    generics.types.r(s)[generic.r(s).index as usize].unwrap_re()
                } else {
                    re
                }
            }
            Re::Internal(_) => unreachable!(),
        }
    }

    fn substitute_inner(&self, target: Ty, self_ty: Ty, generics: GenericInstance) -> Ty {
        let s = &self.session;

        match *target.r(s) {
            TyKind::This => self_ty,
            TyKind::Simple(..) => target,
            TyKind::RawSlice(ty) => {
                self.intern_ty(TyKind::RawSlice(self.substitute_ty(ty, self_ty, generics)))
            }
            TyKind::Adt(def, tys) => self.intern_ty(TyKind::Adt(
                def,
                self.substitute_ty_or_re_list(tys, self_ty, generics),
            )),
            TyKind::Trait(def, tys) => self.intern_ty(TyKind::Trait(
                def,
                self.substitute_ty_or_re_list(tys, self_ty, generics),
            )),
            TyKind::Tuple(tys) => self.intern_ty(TyKind::Tuple(
                self.substitute_ty_list(tys, self_ty, generics),
            )),
            TyKind::FnDef() => todo!(),
            TyKind::Reference(re, ty) => self.intern_ty(TyKind::Reference(
                self.substitute_re(re, generics),
                self.substitute_ty(ty, self_ty, generics),
            )),
            TyKind::Generic(generic) => {
                if *generic.r(s).binder == generics.binder {
                    generics.types.r(s)[generic.r(s).index as usize].unwrap_ty()
                } else {
                    target
                }
            }
        }
    }

    pub fn equate(&self, src: Ty, onto: Ty, variance: Variance) -> EquateResult {
        self.queries
            .equate
            .compute((src, onto, variance), |_| {
                Ok(self.equate_inner(src, onto, variance))
            })
            .unwrap()
    }

    fn equate_inner(&self, src: Ty, onto: Ty, variance: Variance) -> EquateResult {
        let s = &self.session;

        todo!()
    }
}

#[derive(Debug, Copy, Clone)]
pub struct EquateResult {
    pub errors: Obj<[EquateError]>,
    pub internal_re_constraints: Obj<[()]>,
}

#[derive(Debug, Copy, Clone)]
pub struct EquateError {
    pub src: Ty,
    pub onto: Ty,
}
