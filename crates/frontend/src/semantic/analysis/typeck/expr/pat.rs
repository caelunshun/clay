use crate::{
    base::{
        Diag, ErrorGuaranteed,
        arena::{HasInterner as _, HasListInterner, Obj},
        syntax::Span,
    },
    parse::ast::{AstMutability, AstPatStructRest},
    semantic::{
        analysis::typeck::BodyCtxt,
        infer::{ClauseImportEnv, GenericSubst, HrtbUniverse, PrettyFmtOpts, SpannedError},
        syntax::{
            AdtCtorField, AdtCtorInstance, AdtCtorSyntaxStyle, AdtCtorUnresolved, AdtInstance,
            Divergence, HirPat, HirPatKind, HirPatListFrontAndTail, HirPatListFrontAndTailLen,
            HirPatNamedField, InferTyVarSourceInfo, Mutability, Re, RelationMode, Ty, TyKind,
            TyOrRe,
        },
    },
};

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn check_pat_infer(
        &mut self,
        pat: Obj<HirPat>,
        place_divergence: Option<&mut Divergence>,
    ) -> Ty {
        let s = self.session();
        let infer = self.ccx_mut().fresh_ty_infer(
            HrtbUniverse::ROOT,
            InferTyVarSourceInfo::PatType {
                span: pat.r(s).span,
            },
        );

        self.check_pat_demand(pat, infer, place_divergence);
        infer
    }

    pub fn check_pat_demand(
        &mut self,
        pat: Obj<HirPat>,
        demand: Ty,
        place_divergence: Option<&mut Divergence>,
    ) {
        self.check_pat_inner(pat, demand, None, place_divergence)
    }

    fn check_pat_inner(
        &mut self,
        pat: Obj<HirPat>,
        mut demand: Ty,
        mut default_by_ref: Option<Mutability>,
        mut place_divergence: Option<&mut Divergence>,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        match pat.r(s).kind {
            HirPatKind::Hole | HirPatKind::Error(_) => {
                // (trivially allowed)
            }
            HirPatKind::Binding(by_ref, name, binding) => {
                let by_ref = by_ref
                    .as_explicit()
                    .map(AstMutability::strip_span)
                    .or(default_by_ref);

                let local_ty = self.type_of_local(name);
                let bound_ty = if let Some(by_ref) = by_ref {
                    tcx.intern(TyKind::Reference(Re::ERASED, by_ref, demand))
                } else {
                    demand
                };

                self.ccx_mut()
                    .oblige_ty_unifies_ty(local_ty, bound_ty, RelationMode::Equate)
                    // TODO
                    .map({
                        let span = pat.r(s).span;
                        move |_ccx, error| SpannedError(span, error)
                    })
                    .report_loud();

                if let Some(binding) = binding {
                    self.check_pat_inner(binding, demand, default_by_ref, place_divergence);
                }
            }
            HirPatKind::Slice(HirPatListFrontAndTail { front, tail }) => {
                self.peel_references_from_demand_and_normalize(&mut demand, &mut default_by_ref);

                let elem_ty = self.ccx_mut().fresh_ty_infer(
                    HrtbUniverse::ROOT,
                    InferTyVarSourceInfo::PatType {
                        span: pat.r(s).span,
                    },
                );

                let vec_lang_item = self.krate().r(s).lang_items.vec().unwrap();

                self.ccx_mut()
                    .oblige_ty_unifies_ty(
                        demand,
                        tcx.intern(TyKind::Adt(AdtInstance {
                            def: vec_lang_item,
                            params: tcx.intern_list(&[TyOrRe::Ty(elem_ty)]),
                        })),
                        RelationMode::Equate,
                    )
                    // TODO
                    .map({
                        let span = pat.r(s).span;
                        move |_ccx, error| SpannedError(span, error)
                    })
                    .report_loud();

                for &pat in front.r(s) {
                    self.check_pat_inner(
                        pat,
                        elem_ty,
                        default_by_ref,
                        place_divergence.as_deref_mut(),
                    );
                }

                if let Some(tail) = tail {
                    for &pat in tail.r(s) {
                        self.check_pat_inner(
                            pat,
                            elem_ty,
                            default_by_ref,
                            place_divergence.as_deref_mut(),
                        );
                    }
                }
            }
            HirPatKind::Tuple(HirPatListFrontAndTail { front, tail: None }) => {
                self.peel_references_from_demand_and_normalize(&mut demand, &mut default_by_ref);

                let front_infer = front
                    .r(s)
                    .iter()
                    .map(|pat| {
                        self.ccx_mut().fresh_ty_infer(
                            HrtbUniverse::ROOT,
                            InferTyVarSourceInfo::PatType {
                                span: pat.r(s).span,
                            },
                        )
                    })
                    .collect::<Vec<_>>();

                self.ccx_mut()
                    .oblige_ty_unifies_ty(
                        tcx.intern(TyKind::Tuple(tcx.intern_list(&front_infer))),
                        demand,
                        RelationMode::Equate,
                    )
                    // TODO
                    .map({
                        let span = pat.r(s).span;
                        move |_ccx, error| SpannedError(span, error)
                    })
                    .report_loud();

                for (&pat, &demand) in front.r(s).iter().zip(&front_infer) {
                    self.check_pat_inner(
                        pat,
                        demand,
                        default_by_ref,
                        place_divergence.as_deref_mut(),
                    );
                }
            }
            HirPatKind::Tuple(HirPatListFrontAndTail {
                front,
                tail: Some(tail),
            }) => {
                let res = 'check: {
                    self.peel_references_from_demand_and_normalize(
                        &mut demand,
                        &mut default_by_ref,
                    );

                    let TyKind::Tuple(elems) = demand.r(s) else {
                        break 'check Err(Diag::span_err(
                            pat.r(s).span,
                            format_args!(
                                "demand type must be tuple; got {}",
                                self.ccx().pretty(PrettyFmtOpts::default()).wrap(demand)
                            ),
                        )
                        .emit());
                    };

                    let min_matched = front.r(s).len() + tail.r(s).len();

                    if elems.r(s).len() < min_matched {
                        break 'check Err(Diag::span_err(
                            pat.r(s).span,
                            format_args!(
                                "pattern matches tuple with at least {} element{} but \
                                 provided tuple only has {} element{}",
                                min_matched,
                                if min_matched == 1 { "s" } else { "" },
                                elems.r(s).len(),
                                if elems.r(s).len() == 1 { "s" } else { "" },
                            ),
                        )
                        .emit());
                    }

                    for (&pat, &demand) in front.r(s).iter().zip(elems.r(s)) {
                        self.check_pat_inner(
                            pat,
                            demand,
                            default_by_ref,
                            place_divergence.as_deref_mut(),
                        );
                    }

                    for (&pat, &demand) in tail.r(s).iter().zip(elems.r(s).iter().rev()) {
                        self.check_pat_inner(
                            pat,
                            demand,
                            default_by_ref,
                            place_divergence.as_deref_mut(),
                        );
                    }

                    Ok(())
                };

                if let Err(err) = res {
                    self.ccx_mut()
                        .unify_ty_and_ty(
                            demand,
                            tcx.intern(TyKind::Error(err)),
                            RelationMode::Equate,
                        )
                        .unwrap()
                        .report_never();
                }
            }
            HirPatKind::Lit(expr) => {
                self.peel_references_from_demand_and_normalize(&mut demand, &mut default_by_ref);
                self.check_expr_demand(expr, demand).ignore_divergence();
            }
            HirPatKind::Or(patterns) => {
                for &pat in patterns.r(s) {
                    self.check_pat_inner(
                        pat,
                        demand,
                        default_by_ref,
                        place_divergence.as_deref_mut(),
                    );
                }
            }
            HirPatKind::Deref(mutability, pointee_pat) => {
                let pointee_ty = self.ccx_mut().fresh_ty_infer(
                    HrtbUniverse::ROOT,
                    InferTyVarSourceInfo::PatType {
                        span: pat.r(s).span,
                    },
                );

                self.ccx_mut()
                    .oblige_ty_unifies_ty(
                        demand,
                        tcx.intern(TyKind::Reference(Re::ERASED, mutability, pointee_ty)),
                        RelationMode::Equate,
                    )
                    // TODO
                    .map({
                        let span = pat.r(s).span;
                        move |_ccx, error| SpannedError(span, error)
                    })
                    .report_loud();

                self.check_pat_inner(pointee_pat, demand, default_by_ref, place_divergence);
            }
            HirPatKind::AdtUnit(instance) => {
                _ = self.check_pat_ctor(
                    pat,
                    pat.r(s).span,
                    instance,
                    AdtCtorSyntaxStyle::Unit,
                    &mut demand,
                    &mut default_by_ref,
                );
            }
            HirPatKind::AdtTuple(instance, fields) => 'check: {
                // Verify constructor
                let instance_span = pat.r(s).span;

                let Ok(ctor) = self.check_pat_ctor(
                    pat,
                    instance_span,
                    instance,
                    AdtCtorSyntaxStyle::Tuple,
                    &mut demand,
                    &mut default_by_ref,
                ) else {
                    break 'check;
                };

                let adt_item = ctor.def.r(s).owner.item(s);
                let adt_ty = ctor.to_adt_instance_ty(tcx);

                // Verify tuple arity
                let expected_len = ctor.def.r(s).fields.len() as u32;

                let arity_offense = match fields.len(s) {
                    HirPatListFrontAndTailLen::Exactly(v) if v != expected_len => Some((v, "", "")),
                    HirPatListFrontAndTailLen::AtLeast(v) if v > expected_len => {
                        Some((v, " at least", "only "))
                    }
                    _ => None,
                };

                if let Some((child_count, at_least, only)) = arity_offense {
                    Diag::span_err(
                        instance_span,
                        format_args!(
                            "this pattern has{at_least} {child_count} field{}, but the \
                             corresponding tuple {} {only}has {}",
                            if child_count == 1 { "" } else { "s" },
                            ctor.def.r(s).owner.bare_identified_what(s),
                            expected_len,
                        ),
                    )
                    .emit();
                }

                // Check fields
                let front_fields = fields.front.r(s).iter().zip(&ctor.def.r(s).fields);

                let back_fields = fields
                    .tail
                    .iter()
                    .flat_map(|v| v.r(s).iter())
                    .zip(ctor.def.r(s).fields.iter().rev());

                for (&pat, field) in front_fields.chain(back_fields) {
                    if !field.vis.is_visible_to(self.item(), s) {
                        Diag::span_err(
                            pat.r(s).span,
                            format_args!(
                                "field `{}` of {} is not visible to {}",
                                field.idx.raw(),
                                ctor.def.r(s).owner.bare_identified_what(s),
                                self.item().r(s).bare_category_path(s),
                            ),
                        )
                        .emit();
                    }

                    let demand = self.ccx_mut().import_elsewhere(
                        &ClauseImportEnv::new(
                            Some(adt_ty),
                            [GenericSubst::new(adt_item.r(s).generics, ctor.params)],
                        ),
                        *field.ty,
                    );

                    self.check_pat_inner(
                        pat,
                        demand,
                        default_by_ref,
                        place_divergence.as_deref_mut(),
                    );
                }
            }
            HirPatKind::AdtNamed(instance, fields, rest) => 'check: {
                // Verify constructor
                let instance_span = pat.r(s).span;

                let Ok(ctor) = self.check_pat_ctor(
                    pat,
                    instance_span,
                    instance,
                    AdtCtorSyntaxStyle::Named,
                    &mut demand,
                    &mut default_by_ref,
                ) else {
                    break 'check;
                };

                let adt_item = ctor.def.r(s).owner.item(s);
                let adt_ty = ctor.to_adt_instance_ty(tcx);

                // Verify fields
                let field_mapping = self.match_up_ctor_members(
                    ctor.def,
                    fields
                        .r(s)
                        .iter()
                        .map(|&HirPatNamedField { name, pat }| (name, pat))
                        .collect(),
                    match rest {
                        AstPatStructRest::Rest(_) => None,
                        AstPatStructRest::None => Some(instance_span),
                    },
                );

                for (field_idx, pat) in field_mapping {
                    let AdtCtorField { ty, .. } = &ctor.def.r(s).fields[field_idx];

                    let demand = self.ccx_mut().import_elsewhere(
                        &ClauseImportEnv::new(
                            Some(adt_ty),
                            [GenericSubst::new(adt_item.r(s).generics, ctor.params)],
                        ),
                        **ty,
                    );

                    self.check_pat_inner(
                        pat,
                        demand,
                        default_by_ref,
                        place_divergence.as_deref_mut(),
                    );
                }
            }
            HirPatKind::PlaceExpr(place) => {
                self.check_expr_demand(place, demand)
                    .and_do(place_divergence.unwrap());
            }
            HirPatKind::Range(expr) => {
                let res = self.check_range_expr(expr).ignore_divergence();

                if let Some(elem_ty) = res.elem_ty() {
                    self.ccx_mut()
                        .oblige_ty_unifies_ty(demand, elem_ty, RelationMode::Equate)
                        // TODO
                        .map({
                            let span = pat.r(s).span;
                            move |_ccx, error| SpannedError(span, error)
                        })
                        .report_loud();
                }
            }
        }
    }

    fn peel_references_from_demand_and_normalize(
        &mut self,
        demand: &mut Ty,
        default_by_ref: &mut Option<Mutability>,
    ) {
        let s = self.session();

        loop {
            *demand = self.ccx_mut().peel_ty_infer_var_after_poll(*demand);

            let TyKind::Reference(_re, muta, pointee) = *demand.r(s) else {
                break;
            };

            *default_by_ref = Some((default_by_ref.unwrap_or(muta)).min(muta));
            *demand = pointee;
        }
    }

    fn check_pat_ctor(
        &mut self,
        pat: Obj<HirPat>,
        instance_span: Span,
        instance: AdtCtorUnresolved,
        expected_syntax: AdtCtorSyntaxStyle,
        demand: &mut Ty,
        default_by_ref: &mut Option<Mutability>,
    ) -> Result<AdtCtorInstance, ErrorGuaranteed> {
        let s = self.session();
        let tcx = self.tcx();

        let ctor = self.resolve_adt_ctor(instance_span, instance)?;

        self.peel_references_from_demand_and_normalize(demand, default_by_ref);

        self.ccx_mut()
            .oblige_ty_unifies_ty(*demand, ctor.to_adt_instance_ty(tcx), RelationMode::Equate)
            // TODO
            .map({
                let span = pat.r(s).span;
                move |_ccx, error| SpannedError(span, error)
            })
            .report_loud();

        let actual_syntax = ctor.def.r(s).syntax.style();

        if actual_syntax != expected_syntax {
            return Err(Diag::span_err(
                instance_span,
                format_args!(
                    "expected {} constructor but {} has a {} constructor",
                    expected_syntax.style_name(),
                    self.ccx().pretty(PrettyFmtOpts::default()).wrap(ctor.def),
                    actual_syntax.style_name(),
                ),
            )
            .emit());
        }

        Ok(ctor)
    }
}
