use crate::{
    base::{
        Diag, ErrorGuaranteed,
        arena::{HasInterner as _, HasListInterner, LateInit, Obj},
        syntax::{HasSpan, Span},
    },
    parse::{
        ast::{AstMutability, AstPatStructRest},
        token::Ident,
    },
    semantic::{
        analysis::typeck::{BodyCtxt, infra::confirm::ThirExprConfirmedWithTy},
        infer::{ClauseImportEnv, GenericSubst, HrtbUniverse, PrettyFmtOpts, SpannedError},
        syntax::{
            AdtCtorField, AdtCtorInstance, AdtCtorSyntaxStyle, AdtCtorUnresolved, AdtInstance,
            Divergence, HirExpr, HirLocal, HirPat, HirPatKind, HirPatListFrontAndTail,
            HirPatNamedField, InferTyVarSourceInfo, LocalNameIdent, Mutability,
            PatListFrontAndTailLen, Re, RelationMode, ThirBlock, ThirExpr, ThirExprKind,
            ThirLetStmt, ThirPatField, ThirPatKind, ThirStmt, Ty, TyKind, TyOrRe,
        },
    },
    symbol,
};

#[derive(Debug)]
pub struct PatLvalueState {
    pub divergence: Divergence,
    pub temporaries: Vec<PatLvalueTemp>,
}

impl Default for PatLvalueState {
    fn default() -> Self {
        Self {
            divergence: Divergence::MayDiverge,
            temporaries: Vec::new(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct PatLvalueTemp {
    pub stash: Obj<HirLocal>,
    pub place: Obj<HirExpr>,
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn check_expr_inner_assign(
        &mut self,
        expr: Obj<HirExpr>,
        lhs: Obj<HirPat>,
        rhs: Obj<HirExpr>,
        divergence: &mut Divergence,
    ) -> ThirExprConfirmedWithTy {
        let tcx = self.tcx();

        let mut pat_lvalue_state = PatLvalueState::default();
        let pat_ty = self.check_pat_infer(lhs, Some(&mut pat_lvalue_state));

        *divergence &= pat_lvalue_state.divergence;

        self.check_expr_demand(rhs, pat_ty).and_do(divergence);

        let ty = tcx.intern(TyKind::Tuple(tcx.intern_list(&[])));

        self.put_thir_expr(expr, ty, move |bcx| {
            let s = bcx.session();

            bcx.create_assign_expr(expr.r(s).span, lhs, rhs, pat_lvalue_state)
        })
    }

    fn create_assign_expr(
        &mut self,
        span: Span,
        lhs: Obj<HirPat>,
        rhs: Obj<HirExpr>,
        pat_lvalue_state: PatLvalueState,
    ) -> ThirExprKind {
        let s = self.session();
        let tcx = self.tcx();

        let unit_ty = tcx.intern(TyKind::Tuple(tcx.intern_list(&[])));
        let unit_ty_exp = self.ccx_mut().export(span, unit_ty);

        let stmts =
            [ThirStmt::Let(Obj::new(
                ThirLetStmt {
                    span,
                    pat: self.confirm_thir_pat_outer(lhs),
                    init: Some(self.confirm_thir_expr_post(rhs)),
                    else_clause: None,
                },
                s,
            ))]
            .into_iter()
            .chain(pat_lvalue_state.temporaries.into_iter().map(
                |PatLvalueTemp { stash, place }| {
                    let stash = self.confirm_thir_local(stash);

                    ThirStmt::Expr(Obj::new(
                        ThirExpr {
                            span,
                            ty: unit_ty_exp,
                            kind: LateInit::new(ThirExprKind::Assign(
                                self.confirm_thir_expr_post(place),
                                self.create_thir_local_expr(stash.r(s).name.span(), stash),
                            )),
                        },
                        s,
                    ))
                },
            ))
            .collect::<Vec<_>>();

        ThirExprKind::Block(Obj::new(
            ThirBlock {
                span,
                ty: unit_ty_exp,
                stmts,
                last_expr: None,
            },
            s,
        ))
    }

    pub fn check_pat_infer(&mut self, pat: Obj<HirPat>, lvalue: Option<&mut PatLvalueState>) -> Ty {
        let s = self.session();
        let infer = self.ccx_mut().fresh_ty_infer(
            HrtbUniverse::ROOT,
            InferTyVarSourceInfo::PatType {
                span: pat.r(s).span,
            },
        );

        self.check_pat_demand(pat, infer, lvalue);
        infer
    }

    pub fn check_pat_demand(
        &mut self,
        pat: Obj<HirPat>,
        demand: Ty,
        lvalue: Option<&mut PatLvalueState>,
    ) {
        self.check_pat_inner(pat, demand, None, lvalue)
    }

    fn check_pat_inner(
        &mut self,
        pat: Obj<HirPat>,
        mut demand: Ty,
        mut default_by_ref: Option<Mutability>,
        mut lvalues: Option<&mut PatLvalueState>,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        let res = match pat.r(s).kind {
            HirPatKind::Hole | HirPatKind::Error(_) => {
                self.put_thir_pat(pat, demand, move |_bcx| ThirPatKind::Hole)
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
                    self.check_pat_inner(binding, demand, default_by_ref, lvalues);
                }

                self.put_thir_pat(pat, demand, move |bcx| ThirPatKind::Binding {
                    by_ref,
                    local: bcx.confirm_thir_local(name),
                    and_bind: bcx.confirm_opt_thir_pat_outer(binding),
                })
            }
            HirPatKind::Slice(hir_list @ HirPatListFrontAndTail { front, tail }) => {
                self.peel_references_from_demand_and_normalize(
                    pat,
                    &mut demand,
                    &mut default_by_ref,
                );

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
                    self.check_pat_inner(pat, elem_ty, default_by_ref, lvalues.as_deref_mut());
                }

                if let Some(tail) = tail {
                    for &pat in tail.r(s) {
                        self.check_pat_inner(pat, elem_ty, default_by_ref, lvalues.as_deref_mut());
                    }
                }

                self.put_thir_pat(pat, demand, move |bcx| {
                    ThirPatKind::Slice(bcx.confirm_thir_pat_list_front_and_tail_outer(hir_list))
                })
            }
            HirPatKind::Tuple(hir_list @ HirPatListFrontAndTail { front, tail: None }) => {
                self.peel_references_from_demand_and_normalize(
                    pat,
                    &mut demand,
                    &mut default_by_ref,
                );

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

                for (pat, &demand) in hir_list.zip(&front_infer, s) {
                    self.check_pat_inner(pat, demand, default_by_ref, lvalues.as_deref_mut());
                }

                self.put_thir_pat(pat, demand, move |bcx| {
                    ThirPatKind::Tuple(bcx.confirm_thir_pat_list_front_and_tail_outer(hir_list))
                })
            }
            HirPatKind::Tuple(
                hir_list @ HirPatListFrontAndTail {
                    front,
                    tail: Some(tail),
                },
            ) => {
                let res = 'check: {
                    self.peel_references_from_demand_and_normalize(
                        pat,
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

                    for (pat, &demand) in hir_list.zip(elems.r(s), s) {
                        self.check_pat_inner(pat, demand, default_by_ref, lvalues.as_deref_mut());
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

                self.put_thir_pat(pat, demand, move |bcx| {
                    ThirPatKind::Tuple(bcx.confirm_thir_pat_list_front_and_tail_outer(hir_list))
                })
            }
            HirPatKind::Lit(expr) => {
                self.peel_references_from_demand_and_normalize(
                    pat,
                    &mut demand,
                    &mut default_by_ref,
                );
                self.check_expr_demand(expr, demand).ignore_divergence();

                self.put_thir_pat(pat, demand, |bcx| todo!())
            }
            HirPatKind::Or(patterns) => {
                for &pat in patterns.r(s) {
                    self.check_pat_inner(pat, demand, default_by_ref, lvalues.as_deref_mut());
                }

                self.put_thir_pat(pat, demand, move |bcx| {
                    ThirPatKind::Or(bcx.confirm_thir_pat_list_outer(patterns))
                })
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

                self.check_pat_inner(pointee_pat, demand, default_by_ref, lvalues);

                self.put_thir_pat(pat, demand, move |bcx| {
                    ThirPatKind::Deref(bcx.confirm_thir_pat_outer(pointee_pat))
                })
            }
            HirPatKind::AdtUnit(instance) => 'check: {
                let ctor = match self.check_pat_ctor(
                    pat,
                    pat.r(s).span,
                    instance,
                    AdtCtorSyntaxStyle::Unit,
                    &mut demand,
                    &mut default_by_ref,
                ) {
                    Ok(v) => v,
                    Err(err) => break 'check self.put_thir_pat_err(pat, err),
                };

                self.put_thir_pat(pat, demand, move |bcx| {
                    let s = bcx.session();

                    ThirPatKind::Adt(ctor.def, Obj::new_iter([], s))
                })
            }
            HirPatKind::AdtTuple(instance, fields) => 'check: {
                // Verify constructor
                let instance_span = pat.r(s).span;

                let ctor = match self.check_pat_ctor(
                    pat,
                    instance_span,
                    instance,
                    AdtCtorSyntaxStyle::Tuple,
                    &mut demand,
                    &mut default_by_ref,
                ) {
                    Ok(v) => v,
                    Err(err) => break 'check self.put_thir_pat_err(pat, err),
                };

                let adt_item = ctor.def.r(s).owner.item(s);
                let adt_ty = ctor.to_adt_instance_ty(tcx);

                // Verify tuple arity
                let expected_len = ctor.def.r(s).fields.len() as u32;

                let arity_offense = match fields.len(s) {
                    PatListFrontAndTailLen::Exactly(v) if v != expected_len => Some((v, "", "")),
                    PatListFrontAndTailLen::AtLeast(v) if v > expected_len => {
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
                for (pat, field) in fields.zip(&ctor.def.r(s).fields, s) {
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

                    self.check_pat_inner(pat, demand, default_by_ref, lvalues.as_deref_mut());
                }

                self.put_thir_pat(pat, demand, move |bcx| {
                    let s = bcx.session();

                    ThirPatKind::Adt(
                        ctor.def,
                        Obj::new_iter(
                            fields
                                .zip(&ctor.def.r(s).fields, s)
                                .map(|(pat, field)| ThirPatField {
                                    idx: field.idx,
                                    pat: bcx.confirm_thir_pat_outer(pat),
                                }),
                            s,
                        ),
                    )
                })
            }
            HirPatKind::AdtNamed(instance, fields, rest) => 'check: {
                // Verify constructor
                let instance_span = pat.r(s).span;

                let ctor = match self.check_pat_ctor(
                    pat,
                    instance_span,
                    instance,
                    AdtCtorSyntaxStyle::Named,
                    &mut demand,
                    &mut default_by_ref,
                ) {
                    Ok(v) => v,
                    Err(err) => {
                        break 'check self.put_thir_pat_err(pat, err);
                    }
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

                for &(field_idx, pat) in &field_mapping {
                    let AdtCtorField { ty, .. } = &ctor.def.r(s).fields[field_idx];

                    let demand = self.ccx_mut().import_elsewhere(
                        &ClauseImportEnv::new(
                            Some(adt_ty),
                            [GenericSubst::new(adt_item.r(s).generics, ctor.params)],
                        ),
                        **ty,
                    );

                    self.check_pat_inner(pat, demand, default_by_ref, lvalues.as_deref_mut());
                }

                self.put_thir_pat(pat, demand, move |bcx| {
                    let s = bcx.session();

                    ThirPatKind::Adt(
                        ctor.def,
                        Obj::new_iter(
                            field_mapping
                                .into_iter()
                                .map(|(resolved_idx, pat)| ThirPatField {
                                    idx: resolved_idx,
                                    pat: bcx.confirm_thir_pat_outer(pat),
                                }),
                            s,
                        ),
                    )
                })
            }
            HirPatKind::PlaceExpr(place) => {
                let lvalues = lvalues.unwrap();

                self.check_expr_demand(place, demand)
                    .and_do(&mut lvalues.divergence);

                let stash = Obj::new(
                    HirLocal {
                        mutability: Mutability::Not,
                        name: LocalNameIdent::User(Ident::new(place.r(s).span, symbol!("tmp"))),
                    },
                    s,
                );

                let stash_ty = self.type_of_local(stash);

                self.ccx_mut()
                    .oblige_ty_unifies_ty(stash_ty, demand, RelationMode::Equate)
                    .report_never();

                lvalues.temporaries.push(PatLvalueTemp { stash, place });

                self.put_thir_pat(pat, demand, move |bcx| ThirPatKind::Binding {
                    by_ref: None,
                    local: bcx.confirm_thir_local(stash),
                    and_bind: None,
                })
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

                self.put_thir_pat(pat, demand, |bcx| todo!())
            }
        };

        assert_eq!(res.pat, pat);
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

        self.peel_references_from_demand_and_normalize(pat, demand, default_by_ref);

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

    fn peel_references_from_demand_and_normalize(
        &mut self,
        pat: Obj<HirPat>,
        demand: &mut Ty,
        default_by_ref: &mut Option<Mutability>,
    ) {
        let s = self.session();

        loop {
            *demand = self.ccx_mut().peel_ty_infer_var_after_poll(*demand);

            let TyKind::Reference(_re, muta, pointee) = *demand.r(s) else {
                break;
            };

            self.refine_thir_pat(pat, *demand, |_bcx, inner| ThirPatKind::Deref(inner));

            *default_by_ref = Some((default_by_ref.unwrap_or(muta)).min(muta));
            *demand = pointee;
        }
    }
}
