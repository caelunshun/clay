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
            AnyGeneric, BinderSpec, GenericBinder, GenericInstance, ImplDef, OntoInferTyVar, Re,
            TraitClause, TraitClauseList, TraitDef, TraitParam, TraitParamList, Ty, TyKind, TyList,
            TyOrRe, TyOrReList, TypeGeneric,
        },
    },
    utils::hash::FxHashMap,
};

impl TyCtxt {
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
                    TyKind::Simple(..) => target,
                    TyKind::Adt(def, tys) => self.intern_ty(TyKind::Adt(
                        def,
                        self.substitute_ty_or_re_list(tys, self_ty, generics),
                    )),
                    TyKind::Trait(def, clauses) => self.intern_ty(TyKind::Trait(
                        def,
                        self.substitute_clause_list(clauses, self_ty, generics),
                    )),
                    TyKind::Tuple(tys) => self.intern_ty(TyKind::Tuple(
                        self.substitute_ty_list(tys, self_ty, generics),
                    )),
                    TyKind::FnDef() => todo!(),
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
                    TyKind::OntoInferVar(id, clauses) => self.intern_ty(TyKind::OntoInferVar(
                        id,
                        self.substitute_clause_list(clauses, self_ty, generics),
                    )),
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
            TraitClause::Trait(def, params) => TraitClause::Trait(
                def,
                self.substitute_trait_param_list(params, self_ty, generics),
            ),
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

    pub fn instantiate_generic_clauses(
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

                            TraitParam::Equals(TyOrRe::Ty(
                                self.intern_ty(TyKind::Universal(generic)),
                            ))
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
        results: &mut AssignabilityResult,
        max_infer_var: OntoInferTyVar,
    ) {
        let s = &self.session;

        if src == onto {
            // The types are compatible!
            return;
        }

        match (*src.r(s), *onto.r(s)) {
            (TyKind::This, _)
            | (_, TyKind::This)
            | (TyKind::ExplicitInfer, _)
            | (_, TyKind::ExplicitInfer)
            | (TyKind::OntoInferVar(..), _) => unreachable!(),
            (TyKind::Reference(_, src), TyKind::Reference(_, onto)) => {
                self.check_type_assignability_erase_regions(
                    src,
                    onto,
                    binder,
                    results,
                    max_infer_var,
                );
            }
            (TyKind::Adt(src_def, src_args), TyKind::Adt(onto_def, onto_args))
                if src_def == onto_def =>
            {
                for (&src, &onto) in src_args.r(s).iter().zip(onto_args.r(s)) {
                    let (TyOrRe::Ty(src), TyOrRe::Ty(onto)) = (src, onto) else {
                        continue;
                    };

                    self.check_type_assignability_erase_regions(
                        src,
                        onto,
                        binder,
                        results,
                        max_infer_var,
                    );
                }
            }
            (TyKind::Tuple(src), TyKind::Tuple(onto)) if src.r(s).len() == onto.r(s).len() => {
                for (&src, &onto) in src.r(s).iter().zip(onto.r(s)) {
                    self.check_type_assignability_erase_regions(
                        src,
                        onto,
                        binder,
                        results,
                        max_infer_var,
                    );
                }
            }
            (_, TyKind::OntoInferVar(onto_var, clauses)) => {
                if let Some(known_onto) = results.lookup_onto_inference(onto_var) {
                    self.check_type_assignability_erase_regions(
                        src,
                        known_onto,
                        binder,
                        results,
                        max_infer_var,
                    );
                } else {
                    results.record_onto_inference(onto_var, src);

                    for &clause in clauses.r(s) {
                        match clause {
                            TraitClause::Outlives(_) => {
                                // (regions are ignored)
                            }
                            TraitClause::Trait(onto_def, onto_params) => {
                                self.check_trait_assignability_erase_regions(
                                    src,
                                    onto_def,
                                    onto_params,
                                    binder,
                                    results,
                                    max_infer_var,
                                );
                            }
                        }
                    }
                }
            }
            // Omissions okay because of intern equality fast-path:
            //
            // - `(Simple, Simple)`
            // - `(FnDef, FnDef)`
            // - `(Universal, Universal)`
            // - `(Trait, Trait)`
            //
            _ => {
                results.reject(AssignFailure::Structural { src, onto });
            }
        }
    }

    pub fn check_trait_assignability_erase_regions(
        &self,
        src: Ty,
        onto_def: Obj<TraitDef>,
        onto_params: TraitParamList,
        binder: &mut GenericBinder,
        results: &mut AssignabilityResult,
        max_infer_var: OntoInferTyVar,
    ) {
        let s = &self.session;

        // See if the type inherently implements it.
        match *src.r(s) {
            TyKind::Trait(obj, intern) => todo!(),
            TyKind::Universal(obj) => todo!(),
            _ => {}
        }

        // Otherwise, see if an `impl` block can provide it.
        let mut impl_failures = Vec::new();

        for &candidate in onto_def.r(s).impls.iter() {
            let mut sub_results = AssignabilityResult::new_fast();

            // TODO
        }

        results.reject(AssignFailure::NoImpls {
            src,
            onto_def,
            onto_params,
            impl_failures,
        });
    }

    pub fn check_clause_satisfies_clause_erase_regions(
        &self,
        src: TraitClauseList,
        onto_def: Obj<TraitDef>,
        onto_params: TraitParamList,
    ) -> bool {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct AssignabilityResult {
    was_successful: bool,
    failures: Option<Vec<AssignFailure>>,
    onto_inferences: FxHashMap<OntoInferTyVar, Ty>,
}

#[derive(Debug, Clone)]
pub enum AssignFailure {
    Structural {
        src: Ty,
        onto: Ty,
    },
    NoImpls {
        src: Ty,
        onto_def: Obj<TraitDef>,
        onto_params: TraitParamList,
        impl_failures: Vec<ImplFailure>,
    },
}

#[derive(Debug, Clone)]
pub struct ImplFailure {
    pub impl_: Obj<ImplDef>,
    pub inner: Vec<AssignFailure>,
}

impl AssignabilityResult {
    pub fn new_fast() -> Self {
        Self {
            was_successful: true,
            failures: None,
            onto_inferences: FxHashMap::default(),
        }
    }

    pub fn new_slow() -> Self {
        Self {
            was_successful: true,
            failures: Some(Vec::new()),
            onto_inferences: FxHashMap::default(),
        }
    }

    pub fn was_successful(&self) -> bool {
        self.was_successful
    }

    pub fn unwrap_failures(self) -> Vec<AssignFailure> {
        self.failures.unwrap()
    }

    pub fn reject(&mut self, failure: AssignFailure) {
        self.was_successful = false;

        if let Some(failures) = &mut self.failures {
            failures.push(failure);
        }
    }

    pub fn record_onto_inference(&mut self, onto: OntoInferTyVar, ty: Ty) {
        let replaced = self.onto_inferences.insert(onto, ty);
        debug_assert!(replaced.is_none());
    }

    pub fn lookup_onto_inference(&self, var: OntoInferTyVar) -> Option<Ty> {
        self.onto_inferences.get(&var).copied()
    }
}
