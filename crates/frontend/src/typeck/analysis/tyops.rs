use crate::{
    base::arena::{LateInit, Obj},
    typeck::{
        analysis::TyCtxt,
        syntax::{
            AnyGeneric, GenericBinder, GenericInstance, PosInBinder, Re, TraitClause,
            TraitClauseList, TraitParam, TraitParamList, TraitSpec, Ty, TyKind, TyList, TyOrRe,
            TyOrReList,
        },
    },
};
use std::ops::ControlFlow;

impl TyCtxt {
    pub fn seal_generic_binder(&self, binder: GenericBinder) -> Obj<GenericBinder> {
        let s = &self.session;

        let binder = Obj::new(binder, s);

        for (i, generic) in binder.r(s).generics.iter().enumerate() {
            LateInit::init(
                match generic {
                    AnyGeneric::Re(generic) => &generic.r(s).binder,
                    AnyGeneric::Ty(generic) => &generic.r(s).binder,
                },
                PosInBinder {
                    def: binder,
                    idx: i as u32,
                },
            );
        }

        binder
    }

    pub fn substitute_ty_or_re_list(
        &self,
        target: TyOrReList,
        self_ty: Ty,
        generics: GenericInstance,
    ) -> TyOrReList {
        self.queries.substitute_ty_or_re_list.compute_infallible(
            (target, self_ty, generics),
            |_| {
                self.intern_ty_or_re_list(
                    &target
                        .r(&self.session)
                        .iter()
                        .map(|&target| self.substitute_ty_or_re(target, self_ty, generics))
                        .collect::<Vec<_>>(),
                )
            },
        )
    }

    pub fn substitute_ty_or_re(
        &self,
        target: TyOrRe,
        self_ty: Ty,
        generics: GenericInstance,
    ) -> TyOrRe {
        match target {
            TyOrRe::Ty(ty) => TyOrRe::Ty(self.substitute_ty(ty, self_ty, generics)),
            TyOrRe::Re(re) => TyOrRe::Re(self.substitute_re(re, generics)),
        }
    }

    pub fn substitute_ty_list(
        &self,
        target: TyList,
        self_ty: Ty,
        generics: GenericInstance,
    ) -> TyList {
        self.queries
            .substitute_ty_list
            .compute_infallible((target, self_ty, generics), |_| {
                self.intern_tys(
                    &target
                        .r(&self.session)
                        .iter()
                        .map(|&ty| self.substitute_ty(ty, self_ty, generics))
                        .collect::<Vec<_>>(),
                )
            })
    }

    pub fn substitute_ty(&self, target: Ty, self_ty: Ty, generics: GenericInstance) -> Ty {
        self.queries
            .substitute_ty
            .compute_infallible((target, self_ty, generics), |_| {
                let s = &self.session;

                match *target.r(s) {
                    TyKind::This => self_ty,
                    TyKind::Simple(..) | TyKind::Error(..) => target,
                    TyKind::Adt(def, tys) => self.intern_ty(TyKind::Adt(
                        def,
                        self.substitute_ty_or_re_list(tys, self_ty, generics),
                    )),
                    TyKind::Trait(clauses) => self.intern_ty(TyKind::Trait(
                        self.substitute_clause_list(clauses, self_ty, generics),
                    )),
                    TyKind::Tuple(tys) => self.intern_ty(TyKind::Tuple(
                        self.substitute_ty_list(tys, self_ty, generics),
                    )),
                    TyKind::FnDef(..) => target,
                    TyKind::Reference(re, ty) => self.intern_ty(TyKind::Reference(
                        self.substitute_re(re, generics),
                        self.substitute_ty(ty, self_ty, generics),
                    )),
                    TyKind::Universal(generic) => {
                        if generic.r(s).binder.def == generics.binder {
                            generics.substs.r(s)[generic.r(s).binder.idx as usize].unwrap_ty()
                        } else {
                            target
                        }
                    }
                    TyKind::InferVar(..) => unreachable!(),
                    TyKind::ExplicitInfer => unreachable!(),
                }
            })
    }

    pub fn substitute_clause_list(
        &self,
        target: TraitClauseList,
        self_ty: Ty,
        generics: GenericInstance,
    ) -> TraitClauseList {
        self.queries
            .substitute_clause_list
            .compute_infallible((target, self_ty, generics), |_| {
                self.intern_trait_clause_list(
                    &target
                        .r(&self.session)
                        .iter()
                        .map(|&clause| self.substitute_clause(clause, self_ty, generics))
                        .collect::<Vec<_>>(),
                )
            })
    }

    pub fn substitute_clause(
        &self,
        target: TraitClause,
        self_ty: Ty,
        generics: GenericInstance,
    ) -> TraitClause {
        match target {
            TraitClause::Outlives(re) => TraitClause::Outlives(self.substitute_re(re, generics)),
            TraitClause::Trait(spec) => TraitClause::Trait(TraitSpec {
                def: spec.def,
                params: self.substitute_trait_param_list(spec.params, self_ty, generics),
            }),
        }
    }

    pub fn substitute_trait_param_list(
        &self,
        target: TraitParamList,
        self_ty: Ty,
        generics: GenericInstance,
    ) -> TraitParamList {
        self.queries.substitute_trait_param_list.compute_infallible(
            (target, self_ty, generics),
            |_| {
                self.intern_trait_param_list(
                    &target
                        .r(&self.session)
                        .iter()
                        .map(|&target| self.substitute_trait_param(target, self_ty, generics))
                        .collect::<Vec<_>>(),
                )
            },
        )
    }

    pub fn substitute_trait_param(
        &self,
        target: TraitParam,
        self_ty: Ty,
        generics: GenericInstance,
    ) -> TraitParam {
        match target {
            TraitParam::Equals(ty) => {
                TraitParam::Equals(self.substitute_ty_or_re(ty, self_ty, generics))
            }
            TraitParam::Unspecified(clauses) => {
                TraitParam::Unspecified(self.substitute_clause_list(clauses, self_ty, generics))
            }
        }
    }

    pub fn substitute_re(&self, target: Re, generics: GenericInstance) -> Re {
        let s = &self.session;

        match target {
            Re::Gc | Re::ExplicitInfer | Re::Erased => target,
            Re::Generic(generic) => {
                if generic.r(s).binder.def == generics.binder {
                    generics.substs.r(s)[generic.r(s).binder.idx as usize].unwrap_re()
                } else {
                    target
                }
            }
            Re::InferVar(_) => unreachable!(),
        }
    }

    pub fn mentioned_generics<B>(
        &self,
        ty: TyOrRe,
        mut f: impl FnMut(AnyGeneric) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        fn recurse_ty_or_re_list<B>(
            tcx: &TyCtxt,
            ty: TyOrReList,
            f: &mut impl FnMut(AnyGeneric) -> ControlFlow<B>,
        ) -> ControlFlow<B> {
            for &elem in ty.r(&tcx.session) {
                recurse_ty_or_re(tcx, elem, f)?;
            }

            ControlFlow::Continue(())
        }

        fn recurse_ty_list<B>(
            tcx: &TyCtxt,
            ty: TyList,
            f: &mut impl FnMut(AnyGeneric) -> ControlFlow<B>,
        ) -> ControlFlow<B> {
            for &elem in ty.r(&tcx.session) {
                recurse_ty(tcx, elem, f)?;
            }

            ControlFlow::Continue(())
        }

        fn recurse_clauses<B>(
            tcx: &TyCtxt,
            clauses: TraitClauseList,
            f: &mut impl FnMut(AnyGeneric) -> ControlFlow<B>,
        ) -> ControlFlow<B> {
            for &clause in clauses.r(&tcx.session) {
                recurse_clause(tcx, clause, f)?;
            }

            ControlFlow::Continue(())
        }

        fn recurse_clause<B>(
            tcx: &TyCtxt,
            clause: TraitClause,
            f: &mut impl FnMut(AnyGeneric) -> ControlFlow<B>,
        ) -> ControlFlow<B> {
            match clause {
                TraitClause::Outlives(re) => {
                    recurse_re(tcx, re, f)?;
                }
                TraitClause::Trait(spec) => {
                    recurse_trait_spec(tcx, spec, f)?;
                }
            }

            ControlFlow::Continue(())
        }

        fn recurse_trait_spec<B>(
            tcx: &TyCtxt,
            spec: TraitSpec,
            f: &mut impl FnMut(AnyGeneric) -> ControlFlow<B>,
        ) -> ControlFlow<B> {
            for &param in spec.params.r(&tcx.session) {
                recurse_param(tcx, param, f)?;
            }

            ControlFlow::Continue(())
        }

        fn recurse_param<B>(
            tcx: &TyCtxt,
            param: TraitParam,
            f: &mut impl FnMut(AnyGeneric) -> ControlFlow<B>,
        ) -> ControlFlow<B> {
            match param {
                TraitParam::Equals(ty_or_re) => {
                    recurse_ty_or_re(tcx, ty_or_re, f)?;
                }
                TraitParam::Unspecified(clauses) => {
                    recurse_clauses(tcx, clauses, f)?;
                }
            }

            ControlFlow::Continue(())
        }

        fn recurse_ty_or_re<B>(
            tcx: &TyCtxt,
            ty_or_re: TyOrRe,
            f: &mut impl FnMut(AnyGeneric) -> ControlFlow<B>,
        ) -> ControlFlow<B> {
            match ty_or_re {
                TyOrRe::Re(re) => recurse_re(tcx, re, f),
                TyOrRe::Ty(ty) => recurse_ty(tcx, ty, f),
            }
        }

        fn recurse_re<B>(
            _tcx: &TyCtxt,
            re: Re,
            f: &mut impl FnMut(AnyGeneric) -> ControlFlow<B>,
        ) -> ControlFlow<B> {
            match re {
                Re::Gc | Re::InferVar(_) | Re::ExplicitInfer | Re::Erased => {
                    // (empty)
                }
                Re::Generic(generic) => {
                    f(AnyGeneric::Re(generic))?;
                }
            }

            ControlFlow::Continue(())
        }

        fn recurse_ty<B>(
            tcx: &TyCtxt,
            ty: Ty,
            f: &mut impl FnMut(AnyGeneric) -> ControlFlow<B>,
        ) -> ControlFlow<B> {
            match *ty.r(&tcx.session) {
                TyKind::This
                | TyKind::Simple(_)
                | TyKind::FnDef(_)
                | TyKind::ExplicitInfer
                | TyKind::InferVar(_, _)
                | TyKind::Error(_) => {
                    // (empty)
                }
                TyKind::Reference(re, pointee) => {
                    recurse_re(tcx, re, f)?;
                    recurse_ty(tcx, pointee, f)?;
                }
                TyKind::Adt(_, args) => {
                    recurse_ty_or_re_list(tcx, args, f)?;
                }
                TyKind::Trait(clauses) => {
                    recurse_clauses(tcx, clauses, f)?;
                }
                TyKind::Tuple(tys) => {
                    recurse_ty_list(tcx, tys, f)?;
                }
                TyKind::Universal(generic) => {
                    f(AnyGeneric::Ty(generic))?;
                }
            }

            ControlFlow::Continue(())
        }

        recurse_ty_or_re(self, ty, &mut f)
    }
}
