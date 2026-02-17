use crate::{
    base::{
        Diag, LeafDiag,
        arena::{HasInterner as _, Obj},
    },
    parse::token::Ident,
    semantic::{
        analysis::{
            BodyCtxt, ClauseErrorProbe, ClauseImportEnvRef, ClauseOrigin,
            TyFolderInfallibleExt as _, UnboundVarHandlingMode, attempt_deref,
        },
        lower::{
            generics::normalize_positional_generic_arity,
            modules::{FrozenModuleResolver, ParentResolver as _, traits_in_single_scope},
        },
        syntax::{
            AdtCtorSyntax, AdtKind, FnDef, FnInstanceInner, FuncDefOwner, GenericSubst,
            HrtbUniverse, Mutability, Re, RelationMode, SpannedTyOrReList, TraitClause, TraitSpec,
            Ty, TyKind,
        },
    },
    utils::lang::IterEither,
};
use smallvec::SmallVec;

#[derive(Debug, Copy, Clone)]
pub struct LookupMethodResult {
    pub receiver: Ty,
    pub resolution: Obj<FnDef>,
}

impl BodyCtxt<'_, '_> {
    pub fn lookup_field(&mut self, receiver: Ty, name: Ident) -> Option<Ty> {
        let s = self.session();
        let tcx = self.tcx();

        let mut receiver_iter = receiver;

        let name_as_idx = name.text.as_str(s).parse::<u32>().ok();

        loop {
            let receiver = self.ccx_mut().peel_ty_infer_var_after_poll(receiver_iter);

            match *receiver.r(s) {
                TyKind::Adt(instance) => match *instance.def.r(s).kind {
                    AdtKind::Struct(def) => 'search: {
                        let ctor = def.r(s).ctor.r(s);

                        let field = match &ctor.syntax {
                            AdtCtorSyntax::Unit => None,
                            AdtCtorSyntax::Tuple => {
                                name_as_idx.and_then(|idx| ctor.fields.get(idx as usize))
                            }
                            AdtCtorSyntax::Named(fields) => {
                                fields.get(&name.text).copied().map(|idx| &ctor.fields[idx])
                            }
                        };

                        let Some(field) = field else {
                            break 'search;
                        };

                        if !field.vis.is_visible_to(self.item(), s) {
                            break 'search;
                        }

                        let env_args = [GenericSubst {
                            binder: instance.def.r(s).generics,
                            substs: instance.params,
                        }];

                        let env = ClauseImportEnvRef::new(receiver, &env_args);

                        let field = self
                            .ccx_mut()
                            .importer(env, HrtbUniverse::ROOT)
                            .fold(field.ty.value);

                        return Some(field);
                    }
                    AdtKind::Enum(_) => {
                        // (fallthrough)
                    }
                },
                TyKind::Tuple(fields) => {
                    if let Some(name_as_idx) = name_as_idx
                        && let Some(&field_ty) = fields.r(s).get(name_as_idx as usize)
                    {
                        return Some(field_ty);
                    }
                }

                TyKind::Simple(_)
                | TyKind::Reference(_, _, _)
                | TyKind::Trait(_, _, _)
                | TyKind::FnDef(_)
                | TyKind::UniversalVar(_) => {
                    // (fallthrough, no special handling)
                }
                TyKind::SigThis
                | TyKind::SigInfer
                | TyKind::SigGeneric(_)
                | TyKind::SigProject(_)
                | TyKind::SigAlias(_, _)
                | TyKind::HrtbVar(_) => unreachable!(),
                TyKind::InferVar(_) => {
                    return Some(tcx.intern(TyKind::Error(
                        Diag::span_err(name.span, "type must be known by this point").emit(),
                    )));
                }
                TyKind::Error(error) => return Some(tcx.intern(TyKind::Error(error))),
            }

            let Some(next) = attempt_deref(self.ccx_mut(), receiver) else {
                break;
            };

            receiver_iter = next;
        }

        None
    }

    pub fn lookup_method(&mut self, receiver: Ty, name: Ident) -> Option<LookupMethodResult> {
        let s = self.session();
        let tcx = self.tcx();

        let scope_trait_candidates = self.collect_scope_trait_candidates(name);

        let mut receiver_iter = receiver;

        loop {
            self.ccx_mut().poll_obligations();

            let receiver = self
                .ccx()
                .ucx()
                .substitutor(UnboundVarHandlingMode::NormalizeToRoot)
                .fold(receiver_iter);

            if matches!(receiver.r(s), TyKind::InferVar(_) | TyKind::Error(_)) {
                break;
            }

            let generic_clause_candidates = self.collect_generic_clause_candidates(receiver, name);

            if let Some(res) = self.lookup_single_method(
                receiver,
                name,
                &scope_trait_candidates,
                &generic_clause_candidates,
            ) {
                return Some(res);
            }

            if let Some(res) = self.lookup_single_method(
                tcx.intern(TyKind::Reference(Re::Erased, Mutability::Not, receiver)),
                name,
                &scope_trait_candidates,
                &generic_clause_candidates,
            ) {
                return Some(res);
            }

            if let Some(res) = self.lookup_single_method(
                tcx.intern(TyKind::Reference(Re::Erased, Mutability::Mut, receiver)),
                name,
                &scope_trait_candidates,
                &generic_clause_candidates,
            ) {
                return Some(res);
            }

            let Some(next) = attempt_deref(self.ccx_mut(), receiver) else {
                break;
            };

            receiver_iter = next;
        }

        None
    }

    pub fn lookup_type_relative(
        &mut self,
        self_ty: Ty,
        as_trait: Option<TraitSpec>,
        assoc_name: Ident,
        assoc_args: Option<SpannedTyOrReList>,
    ) -> Option<Ty> {
        let s = self.session();
        let tcx = self.tcx();

        let self_ty = self.ccx_mut().peel_ty_infer_var_after_poll(self_ty);

        if let TyKind::Error(err) = *self_ty.r(s) {
            return Some(tcx.intern(TyKind::Error(err)));
        }

        let owner = if let Some(as_trait) = as_trait {
            todo!()
        } else {
            let scope_trait_candidates = self.collect_scope_trait_candidates(assoc_name);
            let generic_clause_candidates =
                self.collect_generic_clause_candidates(self_ty, assoc_name);

            let resolution = self.lookup_single(
                MethodQuery::Function(self_ty),
                assoc_name,
                &scope_trait_candidates,
                &generic_clause_candidates,
            )?;

            self.ccx_mut()
                .instantiate_fn_def_as_blank_owner_infer(resolution, self_ty)
        };

        let early_binder = owner.def(s).r(s).generics;

        let early_args = assoc_args.map(|assoc_args| {
            normalize_positional_generic_arity(
                tcx,
                early_binder,
                None,
                assoc_args.own_span(),
                &assoc_args.iter(tcx).collect::<Vec<_>>(),
            )
            .value
        });

        let instance = tcx.intern(FnInstanceInner { owner, early_args });

        Some(tcx.intern(TyKind::FnDef(instance)))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum MethodQuery {
    Method(Ty),
    Function(Ty),
}

impl<'tcx> BodyCtxt<'tcx, '_> {
    fn collect_inherent_candidates(
        &mut self,
        query: MethodQuery,
        name: Ident,
    ) -> impl Iterator<Item = Obj<FnDef>> + use<'tcx> {
        let tcx = self.tcx();
        let s = self.session();
        let item = self.item();

        let candidates = match query {
            MethodQuery::Method(receiver) => IterEither::Left(
                self.ccx()
                    .coherence()
                    .gather_inherent_impl_method_candidates(tcx, receiver, name.text),
            ),
            MethodQuery::Function(self_ty) => IterEither::Right(
                self.ccx()
                    .coherence()
                    .gather_inherent_impl_function_candidates(tcx, self_ty, name.text),
            ),
        };

        candidates.filter(move |candidate| candidate.r(s).impl_vis.unwrap().is_visible_to(item, s))
    }

    fn collect_scope_trait_candidates(&mut self, name: Ident) -> Vec<Obj<FnDef>> {
        let s = self.session();
        let resolver = FrozenModuleResolver(s);

        resolver
            .scope_components(self.item())
            .into_iter()
            // : Iterator<Item = Obj<Item>>
            .flat_map(|scope| traits_in_single_scope(scope, s).iter().copied())
            // : Iterator<Item = Obj<TraitItem>>
            .filter_map(|def| {
                let &idx = def.r(s).name_to_method.get(&name.text)?;
                Some(def.r(s).methods[idx as usize])
            })
            .collect::<Vec<_>>()
    }

    fn collect_generic_clause_candidates(&mut self, ty: Ty, name: Ident) -> Vec<Obj<FnDef>> {
        let s = self.session();
        let ty = self.ccx_mut().peel_ty_infer_var_after_poll(ty);

        let TyKind::UniversalVar(var) = *ty.r(s) else {
            return Vec::new();
        };

        self.ccx_mut()
            .elaborate_ty_universal_clauses(var)
            .clauses
            .r(s)
            .iter()
            .flat_map(|clause| match clause {
                TraitClause::Outlives(_, _) => None,
                TraitClause::Trait(binder) => Some(binder.inner.def),
            })
            .filter_map(|def| {
                let &idx = def.r(s).name_to_method.get(&name.text)?;
                Some(def.r(s).methods[idx as usize])
            })
            .collect::<Vec<_>>()
    }

    fn lookup_single_method(
        &mut self,
        receiver: Ty,
        name: Ident,
        scope_trait_candidates: &[Obj<FnDef>],
        generic_clause_candidates: &[Obj<FnDef>],
    ) -> Option<LookupMethodResult> {
        self.lookup_single(
            MethodQuery::Method(receiver),
            name,
            scope_trait_candidates,
            generic_clause_candidates,
        )
        .map(|resolution| LookupMethodResult {
            receiver,
            resolution,
        })
    }

    fn lookup_single(
        &mut self,
        query: MethodQuery,
        name: Ident,
        scope_trait_candidates: &[Obj<FnDef>],
        generic_clause_candidates: &[Obj<FnDef>],
    ) -> Option<Obj<FnDef>> {
        let s = self.session();

        // Obtain a list of candidates.
        let inherent_candidates = self.collect_inherent_candidates(query, name);

        let generic_clause_candidates = generic_clause_candidates.iter().copied();
        let scope_trait_candidates = scope_trait_candidates.iter().copied();

        let candidates = inherent_candidates
            .chain(generic_clause_candidates)
            .chain(scope_trait_candidates);

        // Scan for inherent `impl` candidates.
        let mut selections = SmallVec::<[Obj<FnDef>; 1]>::new();

        for candidate in candidates {
            // If we started finding trait candidates and already made an inherent selection, break
            // out.
            if let Some(selection) = selections.first()
                && matches!(*selection.r(s).owner, FuncDefOwner::ImplMethod(_, _))
                && !matches!(*candidate.r(s).owner, FuncDefOwner::ImplMethod(_, _))
            {
                break;
            }

            // See whether receiver is applicable.
            if !self.attempt_single_candidate(candidate, query) {
                continue;
            }

            if selections.iter().all(|&v| candidate != v) {
                selections.push(candidate);
            }
        }

        if selections.len() > 1 {
            let mut diag = Diag::span_err(name.span, "multiple applicable items in scope");

            for (idx, selection) in selections.iter().enumerate() {
                diag.push_child(LeafDiag::span_note(
                    selection.r(s).name.span,
                    format_args!(
                        "candidate #{} is defined in {}",
                        idx + 1,
                        selection.r(s).owner.as_item(s).r(s).bare_category_path(s)
                    ),
                ));
            }

            diag.emit();
        }

        selections.first().copied()
    }

    #[must_use]
    fn attempt_single_candidate(&mut self, candidate: Obj<FnDef>, query: MethodQuery) -> bool {
        let tcx = self.tcx();

        let mut fork = self.ccx().clone().with_silent();

        let probe = ClauseErrorProbe::default();
        let origin = ClauseOrigin::never_printed().with_probe_sink(probe.clone());

        match query {
            MethodQuery::Method(receiver) => {
                let self_ty = fork.fresh_ty_infer(HrtbUniverse::ROOT);
                let expected_owner =
                    fork.instantiate_fn_def_as_blank_owner_infer(candidate, self_ty);

                let expected_instance = tcx.intern(FnInstanceInner {
                    owner: expected_owner,
                    early_args: None,
                });

                let expected_env = fork.instantiate_fn_instance_env_as_infer(
                    &origin,
                    expected_instance,
                    HrtbUniverse::ROOT_REF,
                );

                let expected_receiver = fork.import_fn_instance_receiver_as_infer(
                    expected_env.as_ref(),
                    candidate,
                    HrtbUniverse::ROOT_REF,
                );

                fork.oblige_ty_unifies_ty(
                    origin,
                    receiver,
                    expected_receiver,
                    RelationMode::Equate,
                );
            }
            MethodQuery::Function(self_ty) => {
                let expected_owner =
                    fork.instantiate_fn_def_as_blank_owner_infer(candidate, self_ty);
                let expected_instance = tcx.intern(FnInstanceInner {
                    owner: expected_owner,
                    early_args: None,
                });

                // Call for validation side-effect.
                _ = fork.instantiate_fn_instance_env_as_infer(
                    &origin,
                    expected_instance,
                    HrtbUniverse::ROOT_REF,
                );
            }
        }

        fork.poll_obligations();

        !probe.had_error()
    }
}
