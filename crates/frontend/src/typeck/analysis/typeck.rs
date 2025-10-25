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
            AnyGeneric, BinderSpec, GenericBinder, GenericInstance, ImplDef, ListOfTraitClauseList,
            OntoInferTyVar, Re, TraitClause, TraitClauseList, TraitDef, TraitParam, TraitParamList,
            Ty, TyKind, TyList, TyOrRe, TyOrReList, TypeGeneric,
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
                    TyKind::OntoInferVar(..) => unreachable!(),
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
        binder: &mut GenericBinder,
    ) -> TraitClauseList {
        let s = &self.session;

        let generic = generic.r(s);

        if let Some(v) = LateInit::get(&generic.instantiated_clauses) {
            return *v;
        }

        let clauses = generic
            .user_clauses
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
                                    // TODO: These require some substitutions and super-traits
                                    //  should be revealed.
                                    def.unwrap_ty().r(s).user_clauses,
                                    clauses,
                                ),
                            };

                            // TODO: Better debug names.
                            let generic = Obj::new(
                                TypeGeneric {
                                    span: Span::DUMMY,
                                    ident: Ident {
                                        span: Span::DUMMY,
                                        text: symbol!("?"),
                                        raw: false,
                                    },
                                    binder: LateInit::uninit(),
                                    user_clauses: clauses,
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

    pub fn instantiate_fresh_target_infers(
        &self,
        candidate: Obj<ImplDef>,
        min_infer_var: OntoInferTyVar,
    ) -> (Ty, ListOfTraitClauseList) {
        let s = &self.session;

        self.queries
            .instantiate_fresh_target_infers
            .compute_infallible((candidate, min_infer_var), |_| {
                let mut min_infer_var = min_infer_var;

                // Define fresh variables describing the substitutions to be made.
                let binder = candidate.r(s).generics;
                let substs = binder
                    .r(s)
                    .generics
                    .iter()
                    .map(|generic| match generic {
                        AnyGeneric::Re(_) => TyOrRe::Re(Re::Erased),
                        AnyGeneric::Ty(generic) => {
                            let ty = self.intern_ty(TyKind::OntoInferVar(min_infer_var, *generic));
                            min_infer_var.0 += 1;

                            TyOrRe::Ty(ty)
                        }
                    })
                    .collect::<Vec<_>>();

                let substs = self.intern_ty_or_re_list(&substs);
                let substs = GenericInstance { binder, substs };

                // Substitute the target type
                let target =
                    self.substitute_ty(candidate.r(s).target, self.intern_ty(TyKind::This), substs);

                let clauses = binder
                    .r(s)
                    .generics
                    .iter()
                    .filter_map(|generic| match generic {
                        AnyGeneric::Re(_generic) => None,
                        AnyGeneric::Ty(generic) => Some(self.substitute_clause_list(
                            generic.r(s).user_clauses,
                            target,
                            substs,
                        )),
                    })
                    .collect::<Vec<_>>();

                let clauses = self.intern_list_of_trait_clause_list(&clauses);

                (target, clauses)
            })
    }

    pub fn check_type_assignability_erase_regions(
        &self,
        src: Ty,
        onto: Ty,
        binder: &mut GenericBinder,
        infer_var_clause_stack: &mut Vec<TraitClauseList>,
        infer_var_inferences: &mut FxHashMap<OntoInferTyVar, Ty>,
        failures: &mut Vec<SatisfiabilityFailure>,
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
                    infer_var_clause_stack,
                    infer_var_inferences,
                    failures,
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
                        infer_var_clause_stack,
                        infer_var_inferences,
                        failures,
                    );
                }
            }
            (TyKind::Tuple(src), TyKind::Tuple(onto)) if src.r(s).len() == onto.r(s).len() => {
                for (&src, &onto) in src.r(s).iter().zip(onto.r(s)) {
                    self.check_type_assignability_erase_regions(
                        src,
                        onto,
                        binder,
                        infer_var_clause_stack,
                        infer_var_inferences,
                        failures,
                    );
                }
            }
            (_, TyKind::OntoInferVar(onto_var, _)) => {
                if let Some(known_onto) = infer_var_inferences.get(&onto_var).copied() {
                    self.check_type_assignability_erase_regions(
                        src,
                        known_onto,
                        binder,
                        infer_var_clause_stack,
                        infer_var_inferences,
                        failures,
                    );
                } else {
                    infer_var_inferences.insert(onto_var, src);

                    let onto_clauses = infer_var_clause_stack[onto_var.0 as usize];

                    self.check_clause_list_assignability_erase_regions(
                        src,
                        onto_clauses,
                        binder,
                        infer_var_clause_stack,
                        infer_var_inferences,
                        failures,
                    );
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
                failures.push(SatisfiabilityFailure::Structural { src, onto });
            }
        }
    }

    pub fn check_clause_list_assignability_erase_regions(
        &self,
        src: Ty,
        onto: TraitClauseList,
        binder: &mut GenericBinder,
        infer_var_clause_stack: &mut Vec<TraitClauseList>,
        infer_var_inferences: &mut FxHashMap<OntoInferTyVar, Ty>,
        failures: &mut Vec<SatisfiabilityFailure>,
    ) {
        for &clause in onto.r(&self.session).iter() {
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
                        infer_var_clause_stack,
                        infer_var_inferences,
                        failures,
                    );
                }
            }
        }
    }

    #[expect(clippy::too_many_arguments)]
    pub fn check_trait_assignability_erase_regions(
        &self,
        src: Ty,
        onto_def: Obj<TraitDef>,
        onto_params: TraitParamList,
        binder: &mut GenericBinder,
        infer_var_clause_stack: &mut Vec<TraitClauseList>,
        infer_var_inferences: &mut FxHashMap<OntoInferTyVar, Ty>,
        failures: &mut Vec<SatisfiabilityFailure>,
    ) {
        let s = &self.session;

        // See whether the type itself can provide the implementation.
        let direct_satisfy_failures = match *src.r(s) {
            TyKind::Trait(clauses) => {
                todo!()
            }
            TyKind::Universal(generic) => {
                let src_instantiated = self.instantiate_generic_clauses(generic, binder);

                let mut sub_failures = Vec::new();
                let mut sub_inferences = infer_var_inferences.clone();

                self.check_clause_satisfies_clause_erase_regions(
                    src_instantiated,
                    onto_def,
                    onto_params,
                    binder,
                    infer_var_clause_stack,
                    &mut sub_inferences,
                    &mut sub_failures,
                );

                if sub_failures.is_empty() {
                    *infer_var_inferences = sub_inferences;
                    return;
                }

                Some(sub_failures)
            }
            _ => None,
        };

        // Otherwise, attempt to provide the implementation through an implementation block.
        let mut impl_failures = Vec::new();

        for &candidate in onto_def.r(s).impls.iter() {
            // Replace universal qualifications in `impl` with inference variables
            let (mapped_target, additional_vars) = self.instantiate_fresh_target_infers(
                candidate,
                OntoInferTyVar(infer_var_clause_stack.len() as u32),
            );

            let old_infer_var_stack_len = infer_var_clause_stack.len();
            infer_var_clause_stack.extend_from_slice(additional_vars.r(s));

            // Check impl candidate.
            let mut sub_failures = Vec::new();
            let mut sub_inferences = infer_var_inferences.clone();

            let is_accepted = 'is_accepted: {
                // See whether our target type can even match this `impl` block.
                self.check_type_assignability_erase_regions(
                    src,
                    mapped_target,
                    binder,
                    infer_var_clause_stack,
                    &mut sub_inferences,
                    &mut sub_failures,
                );

                if !sub_failures.is_empty() {
                    break 'is_accepted false;
                }

                // See whether our specific trait clauses can be covered this `impl`.
                // TODO

                true
            };

            infer_var_clause_stack.truncate(old_infer_var_stack_len);

            if is_accepted {
                *infer_var_inferences = sub_inferences;
                return;
            }

            impl_failures.push(ImplFailure {
                impl_: candidate,
                cause: sub_failures,
            });
        }

        failures.push(SatisfiabilityFailure::CannotSatisfy {
            src,
            onto_def,
            onto_params,
            direct_satisfy_failures,
            impl_failures,
        });
    }

    #[expect(clippy::too_many_arguments)]
    pub fn check_clause_satisfies_clause_erase_regions(
        &self,
        src_instantiated: TraitClauseList,
        onto_def: Obj<TraitDef>,
        onto_params: TraitParamList,
        binder: &mut GenericBinder,
        infer_var_clause_stack: &mut Vec<TraitClauseList>,
        infer_var_inferences: &mut FxHashMap<OntoInferTyVar, Ty>,
        failures: &mut Vec<SatisfiabilityFailure>,
    ) {
        let s = &self.session;

        let mut direct_failures = Vec::new();

        for &src in src_instantiated.r(s).iter() {
            match src {
                TraitClause::Outlives(_) => {
                    // (regions are ignored)
                }
                TraitClause::Trait(src_def, src_params) => {
                    if src_def != onto_def {
                        continue;
                    }

                    let mut sub_failures = Vec::new();
                    let mut sub_inferences = infer_var_inferences.clone();

                    for (src_param, onto_param) in src_params.r(s).iter().zip(onto_params.r(s)) {
                        let TraitParam::Equals(src) = *src_param else {
                            unreachable!();
                        };

                        let TyOrRe::Ty(src) = src else {
                            // (regions are ignored)
                            continue;
                        };

                        match onto_param {
                            TraitParam::Equals(onto_ty) => {
                                self.check_type_assignability_erase_regions(
                                    src,
                                    onto_ty.unwrap_ty(),
                                    binder,
                                    infer_var_clause_stack,
                                    &mut sub_inferences,
                                    &mut sub_failures,
                                );
                            }
                            TraitParam::Unspecified(clauses) => {
                                self.check_clause_list_assignability_erase_regions(
                                    src,
                                    *clauses,
                                    binder,
                                    infer_var_clause_stack,
                                    &mut sub_inferences,
                                    &mut sub_failures,
                                );
                            }
                        }
                    }

                    if !sub_failures.is_empty() {
                        direct_failures.push(DirectFailure {
                            src_def,
                            src_params,
                            cause: sub_failures,
                        });

                        continue;
                    }

                    *infer_var_inferences = sub_inferences;
                    return;
                }
            }
        }

        failures.push(SatisfiabilityFailure::CannotDirect {
            src_instantiated,
            onto_def,
            onto_params,
            direct_failures,
        });
    }
}

#[derive(Debug, Clone)]
pub enum SatisfiabilityFailure {
    Structural {
        src: Ty,
        onto: Ty,
    },
    CannotSatisfy {
        src: Ty,
        onto_def: Obj<TraitDef>,
        onto_params: TraitParamList,
        direct_satisfy_failures: Option<Vec<SatisfiabilityFailure>>,
        impl_failures: Vec<ImplFailure>,
    },
    CannotDirect {
        src_instantiated: TraitClauseList,
        onto_def: Obj<TraitDef>,
        onto_params: TraitParamList,
        direct_failures: Vec<DirectFailure>,
    },
}

#[derive(Debug, Clone)]
pub struct ImplFailure {
    pub impl_: Obj<ImplDef>,
    pub cause: Vec<SatisfiabilityFailure>,
}

#[derive(Debug, Clone)]
pub struct DirectFailure {
    pub src_def: Obj<TraitDef>,
    pub src_params: TraitParamList,
    pub cause: Vec<SatisfiabilityFailure>,
}
