use crate::{
    base::{
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    symbol,
    typeck::{
        analysis::TyCtxt,
        syntax::{
            AnyGeneric, BinderSpec, GenericBinder, GenericInstance, Re, TraitClause,
            TraitClauseList, TraitDef, TraitParam, TraitParamList, Ty, TyKind, TyList, TyOrRe,
            TyOrReList, TypeGeneric,
        },
    },
    utils::hash::FxHashMap,
};
use disjoint::DisjointSetVec;

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
            Re::Gc | Re::ExplicitInfer | Re::Erased => re,
            Re::Generic(generic) => {
                if generic.r(s).binder.def == generics.binder {
                    generics.substs.r(s)[generic.r(s).binder.idx as usize].unwrap_re()
                } else {
                    re
                }
            }
            Re::InferVar(_) => unreachable!(),
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
                if generic.r(s).binder.def == generics.binder {
                    generics.substs.r(s)[generic.r(s).binder.idx as usize].unwrap_ty()
                } else {
                    target
                }
            }
            TyKind::ExplicitInfer | TyKind::InferVar(_) => unreachable!(),
        }
    }

    pub fn instantiate_clauses(
        &self,
        generic: Obj<TypeGeneric>,
        span: Span,
        binder: &mut GenericBinder,
    ) -> TraitClauseList {
        let s = &self.session;

        let generic = generic.r(s);

        if let Some(v) = LateInit::get(&generic.instantiated_clauses) {
            return *v;
        }

        let clauses = generic
            .uninstantiated_clauses
            .r(s)
            .iter()
            .map(|clause| match *clause {
                TraitClause::Outlives(re) => TraitClause::Outlives(re),
                TraitClause::Trait(def, params) => {
                    let params = params
                        .r(s)
                        .iter()
                        .zip(&def.r(s).generics.r(s).generics)
                        .map(|(&param, def)| {
                            let clauses = match param {
                                TraitParam::Equals(_) => return param,
                                TraitParam::Unspecified(clauses) => self.join_trait_clause_lists(
                                    def.unwrap_ty().r(s).uninstantiated_clauses,
                                    clauses,
                                ),
                            };

                            let generic = Obj::new(
                                TypeGeneric {
                                    span,
                                    ident: Ident {
                                        span,
                                        text: symbol!("?"),
                                        raw: false,
                                    },
                                    binder: LateInit::uninit(),
                                    uninstantiated_clauses: clauses,
                                    instantiated_clauses: LateInit::uninit(),
                                    is_synthetic: true,
                                },
                                s,
                            );

                            binder.generics.push(AnyGeneric::Ty(generic));

                            TraitParam::Equals(TyOrRe::Ty(self.intern_ty(TyKind::Generic(generic))))
                        })
                        .collect::<Vec<_>>();

                    TraitClause::Trait(def, self.intern_trait_param_list(&params))
                }
            })
            .collect::<Vec<_>>();

        let clauses = self.intern_trait_clause_list(&clauses);

        LateInit::init(&generic.instantiated_clauses, clauses);

        clauses
    }

    pub fn seal_binder(&self, binder: GenericBinder) -> Obj<GenericBinder> {
        let s = &self.session;

        let binder = Obj::new(binder, s);

        for (i, generic) in binder.r(s).generics.iter().enumerate() {
            LateInit::init(
                match generic {
                    AnyGeneric::Re(generic) => &generic.r(s).binder,
                    AnyGeneric::Ty(generic) => &generic.r(s).binder,
                },
                BinderSpec {
                    def: binder,
                    idx: i as u32,
                },
            );
        }

        binder
    }

    pub fn check_type_assignability_erase_regions(
        &self,
        src: Ty,
        onto: Ty,
        binder: &mut GenericBinder,
    ) -> MatchTypesResult {
        let s = &self.session;

        let mut results = MatchTypesResult::default();

        if src == onto {
            return results;
        }

        match (*src.r(s), *onto.r(s)) {
            (_, TyKind::Generic(generic)) => {
                results.union_generic(generic, src);

                for &clause in generic.r(s).uninstantiated_clauses.r(s) {
                    match clause {
                        TraitClause::Outlives(_) => {
                            // (regions are ignored)
                        }
                        TraitClause::Trait(onto_def, onto_params) => {
                            results.join(&self.check_trait_assignability_erase_regions(
                                src,
                                onto_def,
                                onto_params,
                                binder,
                            ));
                        }
                    }
                }
            }
            _ => {
                results.report_mismatch(src, onto);
            }
        }

        results
    }

    pub fn check_trait_assignability_erase_regions(
        &self,
        src: Ty,
        onto_def: Obj<TraitDef>,
        onto_params: TraitParamList,
        binder: &mut GenericBinder,
    ) -> MatchTypesResult {
        let mut results = MatchTypesResult::default();

        results
    }
}

#[derive(Debug, Clone, Default)]
pub struct MatchTypesResult {
    concrete_mismatches: Vec<(Ty, Ty)>,
    concrete_no_impls: Vec<(Ty, Obj<TraitDef>, TraitParamList)>,
    generic_unions: DisjointSetVec<Obj<TypeGeneric>>,
    generic_unions_map: FxHashMap<Obj<TypeGeneric>, usize>,
    generic_equalities: FxHashMap<Obj<TypeGeneric>, Ty>,
}

impl MatchTypesResult {
    pub fn report_mismatch(&mut self, src: Ty, onto: Ty) {
        self.concrete_mismatches.push((src, onto));
    }

    pub fn report_no_impls(&mut self, src: Ty) {}

    pub fn union_generic(&self, generic: Obj<TypeGeneric>, to: Ty) {
        todo!()
    }

    pub fn join(&mut self, other: &MatchTypesResult) {
        todo!()
    }
}
