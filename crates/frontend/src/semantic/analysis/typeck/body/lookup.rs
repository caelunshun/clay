use crate::{
    base::{
        Diag, LeafDiag,
        arena::{HasInterner as _, Obj},
    },
    parse::token::Ident,
    semantic::{
        analysis::{
            BodyCtxt, ClauseErrorProbe, ClauseOrigin, TyFolderInfallibleExt as _,
            UnboundVarHandlingMode, attempt_deref,
        },
        lower::modules::{FrozenModuleResolver, ParentResolver as _, traits_in_single_scope},
        syntax::{
            FnDef, FnInstanceInner, FuncDefOwner, HrtbUniverse, Mutability, Re, RelationMode,
            TraitClause, Ty, TyKind,
        },
    },
};
use smallvec::SmallVec;

#[derive(Debug, Copy, Clone)]
pub struct LookupMethodResult {
    pub receiver: Ty,
    pub resolution: Obj<FnDef>,
}

impl BodyCtxt<'_, '_> {
    pub fn lookup_method(&mut self, receiver: Ty, name: Ident) -> Option<LookupMethodResult> {
        let s = self.session();
        let tcx = self.tcx();
        let resolver = FrozenModuleResolver(s);

        let scope_trait_candidates = resolver
            .scope_components(self.item())
            .into_iter()
            // : Iterator<Item = Obj<Item>>
            .flat_map(|scope| traits_in_single_scope(scope, s).iter().copied())
            // : Iterator<Item = Obj<TraitItem>>
            .filter_map(|def| {
                let &idx = def.r(s).name_to_method.get(&name.text)?;
                Some(def.r(s).methods[idx as usize])
            })
            .collect::<Vec<_>>();

        let mut receiver_iter = receiver;

        loop {
            self.ccx_mut().poll_obligations();

            let receiver = self
                .ccx()
                .ucx()
                .substitutor(UnboundVarHandlingMode::NormalizeToRoot)
                .fold(receiver_iter);

            if let TyKind::InferVar(_) = receiver.r(s) {
                break;
            }

            let generic_clause_candidates = if let TyKind::UniversalVar(var) = *receiver.r(s) {
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
            } else {
                Vec::new()
            };

            if let Some(res) = self.lookup_method_single_receiver(
                receiver,
                name,
                &scope_trait_candidates,
                &generic_clause_candidates,
            ) {
                return Some(res);
            }

            if let Some(res) = self.lookup_method_single_receiver(
                tcx.intern(TyKind::Reference(Re::Erased, Mutability::Not, receiver)),
                name,
                &scope_trait_candidates,
                &generic_clause_candidates,
            ) {
                return Some(res);
            }

            if let Some(res) = self.lookup_method_single_receiver(
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

    fn lookup_method_single_receiver(
        &mut self,
        receiver: Ty,
        name: Ident,
        scope_trait_candidates: &[Obj<FnDef>],
        generic_clause_candidates: &[Obj<FnDef>],
    ) -> Option<LookupMethodResult> {
        let s = self.session();
        let tcx = self.tcx();

        // Obtain a list of candidates.
        let inherent_candidates = self
            .ccx()
            .coherence()
            .gather_inherent_impl_candidates(tcx, receiver, name.text)
            .filter(|candidate| {
                debug_assert!(*candidate.r(s).has_self_param);

                candidate
                    .r(s)
                    .impl_vis
                    .unwrap()
                    .is_visible_to(self.item(), s)
            });

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
            let mut fork = self.ccx().clone();

            let probe = ClauseErrorProbe::default();
            let origin = ClauseOrigin::never_printed().with_probe_sink(probe.clone());

            let expected_owner = fork.instantiate_fn_def_as_owner_infer(candidate);
            let expected_receiver = fork.instantiate_fn_instance_receiver_as_infer(
                &origin,
                tcx.intern(FnInstanceInner {
                    owner: expected_owner,
                    early_args: None,
                }),
                HrtbUniverse::ROOT_REF,
            );

            fork.oblige_ty_unifies_ty(origin, receiver, expected_receiver, RelationMode::Equate);
            fork.poll_obligations();

            if probe.had_error() {
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

        selections
            .first()
            .copied()
            .map(|resolution| LookupMethodResult {
                receiver,
                resolution,
            })
    }
}
