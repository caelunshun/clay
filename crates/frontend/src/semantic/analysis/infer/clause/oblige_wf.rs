//! Logic to implement the well-formed obligation.

use crate::{
    base::{
        analysis::Spanned,
        arena::{HasInterner, Obj},
    },
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnvRef, ClauseOrigin, ClauseOriginKind, HrtbUniverse,
            HrtbUniverseInfo, TyCtxt, TyFoldable, TyVisitable, TyVisitor, TyVisitorInfallibleExt,
        },
        syntax::{
            GenericBinder, GenericSubst, RelationDirection, SpannedAdtInstance, SpannedFnInstance,
            SpannedFnInstanceView, SpannedHrtbBinder, SpannedHrtbBinderKindView,
            SpannedHrtbBinderView, SpannedHrtbDebruijnDefView, SpannedTraitInstance,
            SpannedTraitParamView, SpannedTraitSpec, SpannedTy, SpannedTyOrRe, SpannedTyOrReList,
            SpannedTyView, Ty, TyKind, TyOrRe,
        },
    },
};
use std::{convert::Infallible, ops::ControlFlow};

impl<'tcx> ClauseCx<'tcx> {
    pub fn wf_visitor(&mut self, universe: HrtbUniverse) -> ClauseTyWfVisitor<'_, 'tcx> {
        ClauseTyWfVisitor {
            ccx: self,
            universe,
            clause_applies_to: None,
        }
    }
}

pub struct ClauseTyWfVisitor<'a, 'tcx> {
    pub ccx: &'a mut ClauseCx<'tcx>,
    pub universe: HrtbUniverse,
    pub clause_applies_to: Option<Ty>,
}

impl ClauseTyWfVisitor<'_, '_> {
    pub fn with_clause_applies_to(mut self, ty: Ty) -> Self {
        self.clause_applies_to = Some(ty);
        self
    }
}

impl<'tcx> TyVisitor<'tcx> for ClauseTyWfVisitor<'_, 'tcx> {
    type Break = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn visit_hrtb_binder<T: Copy + TyVisitable + TyFoldable>(
        &mut self,
        binder: SpannedHrtbBinder<T>,
    ) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        let SpannedHrtbBinderView {
            kind,
            inner:
                Spanned {
                    value: _,
                    span_info: inner_span_info,
                },
        } = binder.view(tcx);

        let SpannedHrtbBinderKindView::Imported(defs) = kind.view(tcx) else {
            unreachable!()
        };

        let old_universe = self.universe.clone();
        let new_universe = if defs.is_empty(s) {
            self.universe.clone()
        } else {
            self.universe.clone().nest(HrtbUniverseInfo {
                origin: ClauseOrigin::root_report(ClauseOriginKind::WfHrtb {
                    binder_span: kind.own_span(),
                }),
            })
        };

        self.universe = new_universe;
        {
            let bound = Spanned::new_raw(
                self.ccx
                    .instantiate_hrtb_universal(&self.universe, binder.value),
                inner_span_info,
            );

            self.visit_spanned(bound);

            for def in defs.iter(tcx) {
                let SpannedHrtbDebruijnDefView {
                    spawned_from: _,
                    kind: _,
                    clauses,
                } = def.view(tcx);

                self.visit_spanned(clauses);
            }
        }
        self.universe = old_universe;

        ControlFlow::Continue(())
    }

    fn visit_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
        match ty.view(self.tcx()) {
            SpannedTyView::Trait(_, _, _) => {
                let old_clause_applies_to = self.clause_applies_to.replace(ty.value);
                self.walk_spanned(ty);
                self.clause_applies_to = old_clause_applies_to;
            }
            SpannedTyView::Reference(re, _muta, pointee) => {
                self.ccx.oblige_ty_outlives_re(
                    ClauseOrigin::root_report(ClauseOriginKind::WfForReference {
                        pointee: pointee.own_span(),
                    }),
                    pointee.value,
                    re.value,
                    RelationDirection::LhsOntoRhs,
                );

                self.walk_spanned(ty);
            }

            SpannedTyView::Simple(_)
            | SpannedTyView::Adt(_)
            | SpannedTyView::FnDef(_)
            | SpannedTyView::Tuple(_)
            | SpannedTyView::UniversalVar(_)
            | SpannedTyView::HrtbVar(_)
            | SpannedTyView::Error(_) => {
                self.walk_spanned(ty);
            }
            SpannedTyView::InferVar(_) => {
                // It is assumed that inference variables are checked for well-formed'ness somewhere
                // else.
            }
            SpannedTyView::SigThis
            | SpannedTyView::SigInfer
            | SpannedTyView::SigGeneric(_)
            | SpannedTyView::SigProject(_)
            | SpannedTyView::SigAlias(_, _) => {
                unreachable!()
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        let params = spec
            .view(tcx)
            .params
            .iter(tcx)
            .map(|param| match param.view(tcx) {
                SpannedTraitParamView::Equals(v) => v,
                SpannedTraitParamView::Unspecified(_) => SpannedTyOrRe::new_unspanned(TyOrRe::Ty(
                    self.ccx.fresh_ty_infer(self.universe.clone()),
                )),
            })
            .collect::<Vec<_>>();

        let params = SpannedTyOrReList::alloc_list(spec.own_span(), &params, tcx);

        // Just like in `rustc`, we never produce obligations on the associated types since, if an
        // `impl` is found, we just rely on the fact that `impl` WF checks already validated the
        // type for its clauses and ensure that our `impl` matches what the trait spec said it would
        // contain.
        self.check_generic_values(
            self.clause_applies_to.unwrap(),
            *spec.value.def.r(s).generics,
            [],
            params,
            Some(*spec.value.def.r(s).regular_generic_count),
        );

        self.walk_spanned(spec);

        ControlFlow::Continue(())
    }

    fn visit_trait_instance(&mut self, instance: SpannedTraitInstance) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        self.check_generic_values(
            self.clause_applies_to.unwrap(),
            *instance.value.def.r(s).generics,
            [],
            instance.view(tcx).params,
            None,
        );
        self.walk_spanned(instance);

        ControlFlow::Continue(())
    }

    fn visit_adt_instance(&mut self, instance: SpannedAdtInstance) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        // Check generics
        self.check_generic_values(
            tcx.intern(TyKind::Adt(instance.value)),
            instance.value.def.r(s).generics,
            [],
            instance.view(tcx).params,
            None,
        );

        // Ensure parameter types are also well-formed.
        self.walk_spanned(instance);

        ControlFlow::Continue(())
    }

    fn visit_fn_instance(&mut self, instance: SpannedFnInstance) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        let SpannedFnInstanceView { owner, early_args } = instance.view(tcx);

        // Construct an environment, validating the `owner` in the process.
        let env = self.ccx.instantiate_fn_instance_env_as_infer(
            &ClauseOrigin::root_report(ClauseOriginKind::WfFnDef {
                fn_ty: instance.own_span(),
            }),
            &self.universe,
            instance.value,
        );

        // Validate the `early_args`.
        if let Some(early_args) = early_args {
            self.ccx.oblige_args_meet_binder_clauses(
                &self.universe,
                env.as_ref(),
                &owner.value.def(s).r(s).generics.r(s).defs,
                early_args.value.r(s),
                |_, param_idx, clause_span| {
                    ClauseOrigin::root_report(ClauseOriginKind::WfForGenericParam {
                        use_span: early_args.nth(param_idx, tcx).own_span(),
                        clause_span,
                    })
                },
            );
        }

        // Ensure parameter types are also well-formed.
        self.walk_spanned(instance);

        ControlFlow::Continue(())
    }
}

impl ClauseTyWfVisitor<'_, '_> {
    fn check_generic_values(
        &mut self,
        clause_applies_to: Ty,
        binder: Obj<GenericBinder>,
        extra_def_substs: impl IntoIterator<Item = GenericSubst>,
        all_params: SpannedTyOrReList,
        validate_count: Option<u32>,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        let defs = &binder.r(s).defs[..];
        let defs = match validate_count {
            Some(limit) => &defs[..limit as usize],
            None => defs,
        };

        let validated_params = all_params.value.r(s);
        let validated_params = match validate_count {
            Some(limit) => &validated_params[..limit as usize],
            None => validated_params,
        };

        self.ccx.oblige_args_meet_binder_clauses(
            &self.universe,
            ClauseImportEnvRef::new(
                clause_applies_to,
                &[GenericSubst {
                    binder,
                    substs: all_params.value,
                }]
                .into_iter()
                .chain(extra_def_substs)
                .collect::<Vec<_>>(),
            ),
            defs,
            validated_params,
            |_, param_idx, clause_span| {
                ClauseOrigin::root_report(ClauseOriginKind::WfForGenericParam {
                    use_span: all_params.nth(param_idx, tcx).own_span(),
                    clause_span,
                })
            },
        );
    }
}
