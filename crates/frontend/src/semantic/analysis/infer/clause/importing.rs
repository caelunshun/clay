//! Logic to import a user-written type in a signature or function body into a form the inference
//! context can understand.

use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag,
        analysis::{DebruijnAbsoluteRange, DebruijnTop, Spanned},
        arena::{HasInterner, HasListInterner, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnv, ClauseImportEnvRef, ClauseOrigin, ClauseOriginKind,
            HrtbUniverse, UnifyCxMode,
        },
        syntax::{
            AnyGeneric, GenericBinder, GenericSubst, HrtbBinder, HrtbBinderKind, HrtbDebruijn,
            HrtbDebruijnDef, InferTyVarSourceInfo, Re, SpannedHrtbBinder, SpannedHrtbBinderView,
            SpannedRe, SpannedTy, SpannedTyView, TraitParam, TraitSpec, Ty, TyCtxt, TyFoldable,
            TyFolder, TyFolderExt, TyFolderInfallibleExt, TyFolderPreservesSpans, TyKind, TyOrRe,
            TyOrReKind, TyProjection, TyVisitorInfallibleExt, TypeAliasItem,
        },
    },
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;
use std::{convert::Infallible, mem};

impl<'tcx> ClauseCx<'tcx> {
    pub fn importer<'a>(
        &'a mut self,
        origin: &'a ClauseOrigin,
        universe: HrtbUniverse,
        env: ClauseImportEnvRef<'a>,
    ) -> ClauseCxImporter<'a, 'tcx> {
        ClauseCxImporter {
            ccx: self,
            origin,
            universe,
            env: env.to_owned(),
            hrtb_top: DebruijnTop::default(),
            hrtb_binder_ranges: FxHashMap::default(),
            reentrant_aliases: FxHashMap::default(),
        }
    }
}

pub struct ClauseCxImporter<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    origin: &'a ClauseOrigin,
    universe: HrtbUniverse,
    env: ClauseImportEnv,
    hrtb_top: DebruijnTop,
    hrtb_binder_ranges: FxHashMap<Obj<GenericBinder>, DebruijnAbsoluteRange>,
    reentrant_aliases: FxHashMap<Obj<TypeAliasItem>, ReentrantAliasState>,
}

#[derive(Debug, Copy, Clone)]
enum ReentrantAliasState {
    WaitingForViolation,
    Violated(Span),
}

impl<'tcx> TyFolderPreservesSpans<'tcx> for ClauseCxImporter<'_, 'tcx> {}

impl<'tcx> ClauseCxImporter<'_, 'tcx> {
    fn lookup_generic(&self, generic: AnyGeneric) -> TyOrRe {
        let s = self.session();
        let tcx = self.tcx();

        let kind = generic.kind();
        let pos = generic.binder(s);

        if let Some(binder) = self
            .env
            .sig_generic_substs
            .iter()
            .find(|v| v.binder == pos.def)
        {
            return binder.substs.r(s)[pos.idx as usize];
        }

        if let Some(range) = self.hrtb_binder_ranges.get(&pos.def) {
            let var = HrtbDebruijn(self.hrtb_top.make_relative(range.at(pos.idx as usize)));

            return match kind {
                TyOrReKind::Re => TyOrRe::Re(Re::HrtbVar(var)),
                TyOrReKind::Ty => TyOrRe::Ty(tcx.intern(TyKind::HrtbVar(var))),
            };
        }

        panic!("no substitutions provided for signature generic {generic:?}");
    }
}

impl<'tcx> TyFolder<'tcx> for ClauseCxImporter<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_hrtb_binder<T: Copy + TyFoldable>(
        &mut self,
        binder: SpannedHrtbBinder<T>,
    ) -> Result<HrtbBinder<T>, Self::Error> {
        let s = self.session();
        let tcx = self.tcx();

        let SpannedHrtbBinderView { kind, inner } = binder.view(tcx);

        let HrtbBinderKind::Signature(binder) = kind.value else {
            unreachable!()
        };

        let binder_count = binder.r(s).defs.len();

        // Bring the binder into scope.
        let new_range = self.hrtb_top.move_inwards_by(binder_count);
        let old_range = self.hrtb_binder_ranges.insert(binder, new_range);

        // Fold the inner value and definitions list with a new generic binder available as an HRTB
        // binder.
        let inner = self.fold_spanned(inner);
        let defs = binder
            .r(s)
            .defs
            .iter()
            .map(|def| HrtbDebruijnDef {
                spawned_from: *def,
                kind: def.kind(),
                clauses: self.fold_spanned(def.clauses(s)),
            })
            .collect::<Vec<_>>();

        let defs = tcx.intern_list(&defs);

        // Update the `binder_count` only after we've imported the `defs` since the definition
        // indexing scheme is relative to `binder.inner` to allow mutual recursion among generic
        // definitions.
        match old_range {
            Some(old_range) => {
                *self.hrtb_binder_ranges.get_mut(&binder).unwrap() = old_range;
            }
            None => {
                self.hrtb_binder_ranges.remove(&binder);
            }
        }

        self.hrtb_top.move_outwards_by(binder_count);

        Ok(HrtbBinder {
            kind: HrtbBinderKind::Imported(defs),
            inner,
        })
    }

    fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
        let s = self.session();
        let tcx = self.tcx();

        Ok(match ty.view(tcx) {
            SpannedTyView::SigThis => self.env.self_ty,
            SpannedTyView::SigInfer => self.ccx.fresh_ty_infer(
                self.universe.clone(),
                InferTyVarSourceInfo::Imported {
                    origin: self.origin.clone(),
                    span: ty.own_span(),
                },
            ),
            SpannedTyView::SigGeneric(generic) => {
                self.lookup_generic(AnyGeneric::Ty(generic)).unwrap_ty()
            }
            SpannedTyView::SigProject(TyProjection {
                target,
                spec,
                assoc,
            }) => {
                let target = self.fold(target);
                let spec = self.fold(spec);

                let assoc_infer_ty = self.ccx.fresh_ty_infer(
                    self.universe.clone(),
                    InferTyVarSourceInfo::ProjectionResult {
                        origin: self.origin.clone(),
                        span: ty.own_span(),
                    },
                );
                let spec = {
                    let mut args = spec.params.r(s).to_vec();
                    args[assoc as usize] = TraitParam::Equals(TyOrRe::Ty(assoc_infer_ty));

                    TraitSpec {
                        def: spec.def,
                        params: tcx.intern_list(&args),
                    }
                };

                self.ccx
                    .wf_visitor(self.universe.clone())
                    .with_clause_applies_to(target)
                    .visit_spanned(Spanned::new_saturated(spec, ty.own_span(), tcx));

                self.ccx.oblige_ty_meets_trait_instantiated(
                    self.origin
                        .clone()
                        .child(ClauseOriginKind::InstantiatedProjection {
                            span: ty.own_span(),
                        }),
                    self.universe.clone(),
                    target,
                    spec,
                );

                assoc_infer_ty
            }
            SpannedTyView::SigAlias(def, args) => 'alias: {
                match self.reentrant_aliases.entry(def) {
                    hash_map::Entry::Occupied(entry) => {
                        let entry = entry.into_mut();

                        if matches!(entry, ReentrantAliasState::WaitingForViolation) {
                            *entry = ReentrantAliasState::Violated(ty.own_span());
                        }

                        break 'alias tcx.intern(TyKind::Error(ErrorGuaranteed::new_unchecked()));
                    }
                    hash_map::Entry::Vacant(entry) => {
                        entry.insert(ReentrantAliasState::WaitingForViolation);
                    }
                }

                let args = self.fold(args);

                let old_env = mem::replace(
                    &mut self.env,
                    ClauseImportEnv::new(
                        tcx.intern(TyKind::SigThis),
                        vec![GenericSubst {
                            binder: def.r(s).generics,
                            substs: args,
                        }],
                    ),
                );

                let body = self.fold_spanned(*def.r(s).body);

                self.env = old_env;

                match self.reentrant_aliases.remove(&def).unwrap() {
                    ReentrantAliasState::WaitingForViolation => {
                        // (no violation occurred)
                    }
                    ReentrantAliasState::Violated(span) => {
                        let mut diag = Diag::span_err(
                            ty.own_span(),
                            "attempted to expand recursive type alias",
                        );

                        if ty.own_span() != span {
                            diag.push_child(LeafDiag::span_note(span, "reentered here"));
                        }

                        diag.emit();
                    }
                }

                body
            }

            SpannedTyView::Simple(_)
            | SpannedTyView::Reference(_, _, _)
            | SpannedTyView::Adt(_)
            | SpannedTyView::Trait(_, _, _)
            | SpannedTyView::Tuple(_)
            | SpannedTyView::FnDef(_)
            | SpannedTyView::Error(_) => return self.super_spanned_fallible(ty),

            // These should not appear in an unimported type.
            SpannedTyView::HrtbVar(_)
            | SpannedTyView::InferVar(_)
            | SpannedTyView::UniversalVar(_) => {
                unreachable!()
            }
        })
    }

    fn fold_re(&mut self, re: SpannedRe) -> Result<Re, Self::Error> {
        if self.ccx.mode() == UnifyCxMode::RegionBlind {
            return Ok(Re::Erased);
        }

        Ok(match re.value {
            Re::SigInfer => self.ccx.fresh_re_infer(),
            Re::SigGeneric(generic) => self.lookup_generic(AnyGeneric::Re(generic)).unwrap_re(),
            Re::Gc | Re::Error(_) => {
                return self.super_spanned_fallible(re);
            }
            // These should not appear in an imported type.
            Re::HrtbVar(_) | Re::InferVar(_) | Re::UniversalVar(_) | Re::Erased => unreachable!(),
        })
    }
}
