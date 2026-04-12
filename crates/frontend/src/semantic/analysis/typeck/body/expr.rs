use crate::{
    base::{
        Diag,
        analysis::SpannedViewEncode as _,
        arena::{HasInterner as _, HasListInterner as _, Obj},
        syntax::HasSpan as _,
    },
    parse::ast::{AstLit, AstUnOpKind},
    semantic::{
        analysis::{
            BodyCtxt, ClauseError, ClauseOrigin, ClauseOriginKind, EquateOrSet, HrtbUniverse,
            OverloadResolution, TyFolderInfallibleExt as _, TyVisitorInfallibleExt as _,
            peel_ref_for_prim_op, typeck::body::lookup::LookupMethodResult,
        },
        lower::generics::normalize_positional_generic_arity,
        syntax::{
            AdtInstance, Divergence, FnInstanceInner, HirBlock, HirExpr, HirExprKind,
            HirLabelTargetKind, HirLabelledBlock, HirStmt, InferTyVarSourceInfo, Re, RelationMode,
            SimpleTyKind, SimpleTySet, SpannedFnInstanceView, SpannedFnOwnerView, SpannedTyView,
            TraitParam, TraitSpec, Ty, TyAndDivergence, TyKind, TyOrRe,
        },
    },
};

impl BodyCtxt<'_, '_> {
    pub fn check_block_with_no_final_expr(&mut self, block: Obj<HirBlock>) -> Divergence {
        let s = self.session();

        let mut divergence = Divergence::MayDiverge;
        self.check_block_stmts(&block.r(s).stmts, &mut divergence);

        if let Some(last_expr) = block.r(s).last_expr {
            Diag::span_err(
                last_expr.r(s).span,
                "trailing block expression not expected",
            )
            .emit();
        }

        divergence
    }

    pub fn check_block_stmts(&mut self, stmts: &[HirStmt], divergence: &mut Divergence) {
        let s = self.session();

        for stmt in stmts {
            match stmt {
                HirStmt::Expr(expr) => {
                    self.check_expr(*expr, None).and_do(divergence);
                }
                HirStmt::Let(stmt) => {
                    let ascription = if let Some(ascription) = stmt.r(s).ascription {
                        let import_env = self.import_env;

                        let ascription = self
                            .ccx_mut()
                            .importer(
                                &ClauseOrigin::empty_report(),
                                HrtbUniverse::ROOT,
                                import_env,
                            )
                            .fold_preserved(ascription);

                        self.ccx_mut()
                            .wf_visitor(HrtbUniverse::ROOT)
                            .visit_spanned(ascription);

                        if let Some(init) = stmt.r(s).init {
                            self.check_expr_demand(init, ascription.value)
                                .and_do(divergence);
                        }

                        ascription.value
                    } else if let Some(init) = stmt.r(s).init {
                        self.check_expr(init, None).and_do(divergence)
                    } else {
                        self.ccx_mut().fresh_ty_infer(
                            HrtbUniverse::ROOT,
                            InferTyVarSourceInfo::PatType {
                                span: stmt.r(s).pat.r(s).span,
                            },
                        )
                    };

                    self.check_pat_demand(stmt.r(s).pat, ascription, Some(divergence));

                    if let Some(else_clause) = stmt.r(s).else_clause {
                        let divergence = self.check_block_with_no_final_expr(else_clause);

                        if divergence != Divergence::MustDiverge {
                            Diag::span_err(else_clause.r(s).span, "`else` block must diverge")
                                .emit();
                        }
                    }
                }
            }
        }
    }

    pub fn check_expr_inner(
        &mut self,
        expr: Obj<HirExpr>,
        demand_hint: Option<Ty>,
    ) -> TyAndDivergence {
        let s = self.session();
        let tcx = self.tcx();

        let mut divergence = Divergence::MayDiverge;
        let ty = match *expr.r(s).kind {
            HirExprKind::Array(elems) => {
                let elem = if elems.r(s).is_empty() {
                    self.ccx_mut().fresh_ty_infer(
                        HrtbUniverse::ROOT,
                        InferTyVarSourceInfo::EmptyArrayElem {
                            span: expr.r(s).span,
                        },
                    )
                } else {
                    self.check_exprs_equate(elems.r(s).iter().copied())
                        .and_do(&mut divergence)
                };

                let vec_lang_item = self.krate().r(s).lang_items.vec().unwrap();

                tcx.intern(TyKind::Adt(AdtInstance {
                    def: vec_lang_item,
                    params: tcx.intern_list(&[TyOrRe::Ty(elem)]),
                }))
            }
            HirExprKind::Call(callee, actual_args) => 'call: {
                let callee = self.check_expr(callee, None).and_do(&mut divergence);

                if let TyKind::Error(err) =
                    *self.ccx_mut().peel_ty_infer_var_after_poll(callee).r(s)
                {
                    for &actual in actual_args.r(s) {
                        self.check_expr(actual, None).and_do(&mut divergence);
                    }

                    break 'call tcx.intern(TyKind::Error(err));
                }

                let site_span = expr.r(s).span;
                let fn_once_trait = self.krate().r(s).lang_items.fn_once_trait().unwrap();
                let input_ty = self.ccx_mut().fresh_ty_infer(
                    HrtbUniverse::ROOT,
                    InferTyVarSourceInfo::FunctionArgs { span: site_span },
                );

                let output_ty = self.ccx_mut().fresh_ty_infer(
                    HrtbUniverse::ROOT,
                    InferTyVarSourceInfo::FunctionRetVal { span: site_span },
                );

                self.ccx_mut().oblige_ty_meets_trait_instantiated(
                    ClauseOrigin::root_report(ClauseOriginKind::FunctionCall { site_span }),
                    HrtbUniverse::ROOT,
                    callee,
                    TraitSpec {
                        def: fn_once_trait,
                        params: tcx.intern_list(&[
                            TraitParam::Equals(TyOrRe::Ty(input_ty)),
                            TraitParam::Equals(TyOrRe::Ty(output_ty)),
                        ]),
                    },
                );

                let TyKind::Tuple(expected_args) =
                    self.ccx_mut().peel_ty_infer_var_after_poll(input_ty).r(s)
                else {
                    break 'call tcx.intern(TyKind::Error(
                        Diag::span_err(site_span, "annotations needed on input type").emit(),
                    ));
                };

                if expected_args.r(s).len() != actual_args.r(s).len() {
                    break 'call tcx.intern(TyKind::Error(
                        Diag::span_err(site_span, "argument count mismatch").emit(),
                    ));
                }

                for (&actual, &expected) in actual_args.r(s).iter().zip(expected_args.r(s)) {
                    self.check_expr_demand(actual, expected)
                        .and_do(&mut divergence);
                }

                output_ty
            }
            HirExprKind::MethodCall {
                receiver,
                name,
                generics,
                args,
            } => 'call: {
                let receiver_span = receiver.r(s).span;
                let receiver = self.check_expr(receiver, None).and_do(&mut divergence);
                let receiver = self.ccx_mut().peel_ty_infer_var_after_poll(receiver);

                let env = self.import_env;
                let generics = generics.map(|generics| {
                    let out = self
                        .ccx_mut()
                        .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                        .fold_preserved(generics);

                    self.ccx_mut()
                        .wf_visitor(HrtbUniverse::ROOT)
                        .visit_spanned(out);

                    out
                });

                match *receiver.r(s) {
                    TyKind::InferVar(_) => {
                        break 'call tcx.intern(TyKind::Error(
                            Diag::span_err(
                                receiver_span,
                                "type of receiver must be known by this point",
                            )
                            .emit(),
                        ));
                    }
                    TyKind::Error(error) => {
                        break 'call tcx.intern(TyKind::Error(error));
                    }
                    _ => {
                        // (fallthrough)
                    }
                }

                let Some(LookupMethodResult {
                    receiver,
                    resolution,
                }) = self.lookup_method(receiver, name)
                else {
                    break 'call tcx.intern(TyKind::Error(
                        Diag::span_err(name.span, "failed to find applicable method").emit(),
                    ));
                };

                let self_ty = self.ccx_mut().fresh_ty_infer(
                    HrtbUniverse::ROOT,
                    InferTyVarSourceInfo::MethodReceiver { span: name.span },
                );

                let owner = self
                    .ccx_mut()
                    .instantiate_fn_def_as_blank_owner_infer(resolution, self_ty);

                let generics = generics.map(|generics| {
                    normalize_positional_generic_arity(
                        tcx,
                        owner.def(s).r(s).generics,
                        None,
                        generics.own_span(),
                        &generics.iter(tcx).collect::<Vec<_>>(),
                    )
                    .value
                });

                let instance = tcx.intern(FnInstanceInner {
                    owner,
                    early_args: generics,
                });

                let instance_env = self.ccx_mut().instantiate_fn_instance_env_as_infer(
                    &ClauseOrigin::root_report(ClauseOriginKind::FunctionCall {
                        site_span: name.span,
                    }),
                    HrtbUniverse::ROOT_REF,
                    instance,
                );

                let (expected_args, expected_output) = self.ccx_mut().import_fn_instance_sig(
                    &ClauseOrigin::empty_report(),
                    HrtbUniverse::ROOT_REF,
                    instance_env.as_ref(),
                    resolution,
                );

                let (self_ty, expected_args) = expected_args.r(s).split_first().unwrap();

                self.ccx_mut().oblige_ty_unifies_ty(
                    ClauseOrigin::root_report(ClauseOriginKind::FunctionCall {
                        site_span: name.span,
                    }),
                    *self_ty,
                    receiver,
                    RelationMode::Equate,
                );

                if expected_args.len() != args.r(s).len() {
                    break 'call tcx.intern(TyKind::Error(
                        Diag::span_err(name.span, "argument count mismatch").emit(),
                    ));
                }

                for (&actual, &expected) in args.r(s).iter().zip(expected_args) {
                    self.check_expr_demand(actual, expected)
                        .and_do(&mut divergence);
                }

                expected_output
            }
            HirExprKind::Tuple(children) => {
                let children = children
                    .r(s)
                    .iter()
                    .map(|&expr| self.check_expr(expr, None).and_do(&mut divergence))
                    .collect::<Vec<_>>();

                tcx.intern(TyKind::Tuple(tcx.intern_list(&children)))
            }
            HirExprKind::Binary(kind, lhs, rhs) => 'op: {
                let lhs = self.check_expr(lhs, None).and_do(&mut divergence);
                let rhs = self.check_expr(rhs, None).and_do(&mut divergence);

                let kind_info = self.decode_bin_op_kind(kind.kind);
                let origin =
                    ClauseOrigin::root_report(ClauseOriginKind::Arithmetic { op_span: kind.span });

                // Attempt a primitive operation.
                let mut prim_fork = self.ccx().clone();

                let fallback_err = 'try_prim: {
                    let lhs = peel_ref_for_prim_op(&mut prim_fork, lhs);
                    let rhs = peel_ref_for_prim_op(&mut prim_fork, rhs);

                    if let Err(err) = prim_fork.unify_ty_and_simple_set(&origin, lhs, kind_info.lhs)
                    {
                        break 'try_prim ClauseError::TyAndSimpleTySetUnifyError(err);
                    }

                    match kind_info.rhs {
                        EquateOrSet::EqualsLhs => {
                            if let Err(err) =
                                prim_fork.unify_ty_and_ty(&origin, lhs, rhs, RelationMode::Equate)
                            {
                                break 'try_prim ClauseError::TyAndTyUnifyError(*err);
                            }
                        }
                        EquateOrSet::Unrelated(rhs_set) => {
                            if let Err(err) =
                                prim_fork.unify_ty_and_simple_set(&origin, lhs, rhs_set)
                            {
                                break 'try_prim ClauseError::TyAndSimpleTySetUnifyError(err);
                            }
                        }
                    }

                    *self.ccx_mut() = prim_fork;
                    self.overload_resolutions
                        .insert(expr, OverloadResolution::Primitive);

                    break 'op lhs;
                };

                // Otherwise, attempt to perform an overloaded operation.
                if let Some(overload) = kind_info.overload {
                    let result_ty = self.ccx_mut().fresh_ty_infer(
                        HrtbUniverse::ROOT,
                        InferTyVarSourceInfo::OverloadedResult { span: kind.span },
                    );

                    self.ccx_mut().oblige_ty_meets_trait_instantiated(
                        origin,
                        HrtbUniverse::ROOT,
                        lhs,
                        TraitSpec {
                            def: overload,
                            params: tcx.intern_list(&[
                                TraitParam::Equals(TyOrRe::Ty(rhs)),
                                TraitParam::Equals(TyOrRe::Ty(result_ty)),
                            ]),
                        },
                    );

                    self.overload_resolutions
                        .insert(expr, OverloadResolution::Call);

                    break 'op result_ty;
                }

                let error = fallback_err.emit(&prim_fork);

                self.overload_resolutions
                    .insert(expr, OverloadResolution::Error(error));

                tcx.intern(TyKind::Error(error))
            }
            HirExprKind::Unary(kind, lhs) => 'op: {
                let lhs_ty = self.check_expr(lhs, None).and_do(&mut divergence);

                let kind_info = self.decode_un_op_kind(kind);
                let origin = ClauseOrigin::root_report(ClauseOriginKind::Arithmetic {
                    op_span: lhs.r(s).span,
                });

                // Attempt a primitive operation.
                let fallback_err = {
                    let lhs_ty = peel_ref_for_prim_op(self.ccx_mut(), lhs_ty);

                    match self
                        .ccx_mut()
                        .unify_ty_and_simple_set(&origin, lhs_ty, kind_info.lhs)
                    {
                        Ok(()) => {
                            self.overload_resolutions
                                .insert(expr, OverloadResolution::Primitive);

                            break 'op lhs_ty;
                        }
                        Err(err) => err,
                    }
                };

                if kind == AstUnOpKind::Deref
                    && let lhs_ty = self.ccx_mut().peel_ty_infer_var_after_poll(lhs_ty)
                    && let TyKind::Reference(_re, _muta, pointee) = *lhs_ty.r(s)
                {
                    self.overload_resolutions
                        .insert(expr, OverloadResolution::Primitive);

                    break 'op pointee;
                }

                // Otherwise, attempt to perform an overloaded operation.
                if let Some(overload) = kind_info.overload {
                    let result_ty = self.ccx_mut().fresh_ty_infer(
                        HrtbUniverse::ROOT,
                        InferTyVarSourceInfo::OverloadedResult {
                            span: expr.r(s).span,
                        },
                    );

                    self.ccx_mut().oblige_ty_meets_trait_instantiated(
                        origin,
                        HrtbUniverse::ROOT,
                        lhs_ty,
                        TraitSpec {
                            def: overload,
                            params: tcx.intern_list(&[TraitParam::Equals(TyOrRe::Ty(result_ty))]),
                        },
                    );

                    self.overload_resolutions
                        .insert(expr, OverloadResolution::Call);

                    break 'op result_ty;
                }

                let error = fallback_err.emit(self.ccx());

                self.overload_resolutions
                    .insert(expr, OverloadResolution::Error(error));

                tcx.intern(TyKind::Error(error))
            }
            HirExprKind::Literal(lit) => match lit {
                AstLit::Number(_) => {
                    // TODO: Register the correct inference constraints.
                    let var = self.ccx.fresh_ty_infer_var_restricted(
                        HrtbUniverse::ROOT,
                        InferTyVarSourceInfo::Literal { span: lit.span() },
                        SimpleTySet::INT,
                    );
                    self.int_infers.push(var);
                    tcx.intern(TyKind::InferVar(var))
                }
                AstLit::Char(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Char)),
                AstLit::String(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Str)),
                AstLit::Bool(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Bool)),
            },
            HirExprKind::FnItemLit(def, early_args) => {
                let env = self.import_env;
                let early_args = early_args.map(|early_args| {
                    self.ccx_mut()
                        .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                        .fold_preserved(early_args)
                });

                let fn_ty = SpannedTyView::FnDef(
                    SpannedFnInstanceView {
                        owner: SpannedFnOwnerView::Item(def).encode(expr.r(s).span, tcx),
                        early_args,
                    }
                    .encode(expr.r(s).span, tcx),
                )
                .encode(expr.r(s).span, tcx);

                self.ccx_mut()
                    .wf_visitor(HrtbUniverse::ROOT)
                    .visit_spanned(fn_ty);

                fn_ty.value
            }
            HirExprKind::TypeRelative {
                self_ty,
                as_trait,
                assoc_name,
                assoc_args,
            } => 'res: {
                let env = self.import_env;

                let self_ty = self
                    .ccx_mut()
                    .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                    .fold_preserved(self_ty);

                self.ccx_mut()
                    .wf_visitor(HrtbUniverse::ROOT)
                    .visit_spanned(self_ty);

                let as_trait = as_trait.map(|as_trait| {
                    let out = self
                        .ccx_mut()
                        .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                        .fold_preserved(as_trait);

                    self.ccx_mut()
                        .wf_visitor(HrtbUniverse::ROOT)
                        .with_clause_applies_to(self_ty.value)
                        .visit_spanned(out);

                    out.value
                });

                let assoc_args = assoc_args.map(|assoc_args| {
                    let out = self
                        .ccx_mut()
                        .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                        .fold_preserved(assoc_args);

                    self.ccx_mut()
                        .wf_visitor(HrtbUniverse::ROOT)
                        .visit_spanned(out);

                    out
                });

                let Some(resolution) =
                    self.lookup_type_relative(self_ty.value, as_trait, assoc_name, assoc_args)
                else {
                    break 'res tcx.intern(TyKind::Error(
                        Diag::span_err(assoc_name.span, "not found").emit(),
                    ));
                };

                resolution
            }
            HirExprKind::Cast(expr, as_ty) => {
                let env = self.import_env;
                let as_ty = self
                    .ccx_mut()
                    .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                    .fold_preserved(as_ty);

                self.ccx_mut()
                    .wf_visitor(HrtbUniverse::ROOT)
                    .visit_spanned(as_ty);

                self.check_expr_demand(expr, as_ty.value)
                    .and_do(&mut divergence)
            }
            HirExprKind::If {
                cond,
                truthy,
                falsy,
            } => {
                self.check_expr_demand(cond, tcx.intern(TyKind::Simple(SimpleTyKind::Bool)))
                    .and_do(&mut divergence);

                self.check_exprs_equate([Some(truthy), falsy].into_iter().flatten())
                    .and_do(&mut divergence)
            }
            HirExprKind::While(cond, block) => {
                self.check_expr_demand(cond, tcx.intern(TyKind::Simple(SimpleTyKind::Bool)))
                    .and_do(&mut divergence);

                self.check_block_with_no_final_expr(block);

                tcx.intern(TyKind::Tuple(tcx.intern_list(&[])))
            }
            HirExprKind::Let(pat, expr) => {
                let scrutinee = self.check_expr(expr, None).and_do(&mut divergence);
                self.check_pat_demand(pat, scrutinee, Some(&mut divergence));

                tcx.intern(TyKind::Simple(SimpleTyKind::Bool))
            }
            HirExprKind::ForLoop { pat, iter, body } => {
                let iter_ty = self.check_expr(iter, None).and_do(&mut divergence);
                let elem_ty = self.ccx_mut().fresh_ty_infer(
                    HrtbUniverse::ROOT,
                    InferTyVarSourceInfo::ForLoopElem {
                        span: pat.r(s).span,
                    },
                );
                let into_iter_trait = self.krate().r(s).lang_items.into_iterator_trait().unwrap();

                self.ccx_mut().oblige_ty_meets_trait_instantiated(
                    ClauseOrigin::root_report(ClauseOriginKind::ForLoopIter {
                        iter_span: iter.r(s).span,
                    }),
                    HrtbUniverse::ROOT,
                    iter_ty,
                    TraitSpec {
                        def: into_iter_trait,
                        params: tcx.intern_list(&[
                            TraitParam::Unspecified(tcx.intern_list(&[])),
                            TraitParam::Equals(TyOrRe::Ty(elem_ty)),
                        ]),
                    },
                );

                self.check_pat_demand(pat, elem_ty, Some(&mut divergence));

                self.check_block_with_no_final_expr(body);

                tcx.intern(TyKind::Tuple(tcx.intern_list(&[])))
            }
            HirExprKind::Loop(block) => {
                let label = HirLabelledBlock {
                    target: expr,
                    kind: HirLabelTargetKind::Loop,
                };

                self.block_break_demands.insert(label, None);
                self.check_block_with_no_final_expr(block);

                if let Some(break_ty) = self.block_break_demands[&label] {
                    break_ty
                } else {
                    tcx.intern(TyKind::Simple(SimpleTyKind::Never))
                }
            }
            HirExprKind::Match(scrutinee, arms) => todo!(),
            HirExprKind::Block(block) => {
                let label = HirLabelledBlock {
                    target: expr,
                    kind: HirLabelTargetKind::Block,
                };

                self.block_break_demands.insert(label, demand_hint);
                self.check_block_stmts(&block.r(s).stmts, &mut divergence);

                if let Some(last_expr) = block.r(s).last_expr {
                    if let Some(demand) = self.block_break_demands[&label] {
                        self.check_expr_demand(last_expr, demand)
                            .and_do(&mut divergence)
                    } else {
                        self.check_expr(last_expr, demand_hint)
                            .and_do(&mut divergence)
                    }
                } else {
                    if let Some(demand) = self.block_break_demands[&label] {
                        demand
                    } else if divergence.must_diverge() {
                        tcx.intern(TyKind::Simple(SimpleTyKind::Never))
                    } else {
                        tcx.intern(TyKind::Tuple(tcx.intern_list(&[])))
                    }
                }
            }
            HirExprKind::Assign(pat, expr) => {
                let pat_ty = self.check_pat_infer(pat, Some(&mut divergence));
                self.check_expr_demand(expr, pat_ty).and_do(&mut divergence);

                tcx.intern(TyKind::Tuple(tcx.intern_list(&[])))
            }
            HirExprKind::AssignOp(kind, lhs, rhs) => {
                'assign: {
                    let lhs = self.check_pat_infer(lhs, Some(&mut divergence));
                    let rhs = self.check_expr(rhs, None).and_do(&mut divergence);

                    let kind_info = self.decode_assign_op_kind(kind);
                    let origin = ClauseOrigin::root_report(ClauseOriginKind::Arithmetic {
                        op_span: expr.r(s).span,
                    });

                    // Attempt a primitive operation.
                    let mut prim_fork = self.ccx().clone();

                    let fallback_err = 'try_prim: {
                        let lhs = peel_ref_for_prim_op(&mut prim_fork, lhs);
                        let rhs = peel_ref_for_prim_op(&mut prim_fork, rhs);

                        if let Err(err) =
                            prim_fork.unify_ty_and_simple_set(&origin, lhs, kind_info.lhs)
                        {
                            break 'try_prim ClauseError::TyAndSimpleTySetUnifyError(err);
                        }

                        match kind_info.rhs {
                            EquateOrSet::EqualsLhs => {
                                if let Err(err) = prim_fork.unify_ty_and_ty(
                                    &origin,
                                    lhs,
                                    rhs,
                                    RelationMode::Equate,
                                ) {
                                    break 'try_prim ClauseError::TyAndTyUnifyError(*err);
                                }
                            }
                            EquateOrSet::Unrelated(rhs_set) => {
                                if let Err(err) =
                                    prim_fork.unify_ty_and_simple_set(&origin, lhs, rhs_set)
                                {
                                    break 'try_prim ClauseError::TyAndSimpleTySetUnifyError(err);
                                }
                            }
                        }

                        *self.ccx_mut() = prim_fork;
                        break 'assign;
                    };

                    // Otherwise, attempt to perform an overloaded operation.
                    if let Some(overload) = kind_info.overload {
                        let result_ty = self.ccx_mut().fresh_ty_infer(
                            HrtbUniverse::ROOT,
                            InferTyVarSourceInfo::OverloadedResult {
                                span: expr.r(s).span,
                            },
                        );

                        self.ccx_mut().oblige_ty_meets_trait_instantiated(
                            origin,
                            HrtbUniverse::ROOT,
                            lhs,
                            TraitSpec {
                                def: overload,
                                params: tcx.intern_list(&[
                                    TraitParam::Equals(TyOrRe::Ty(rhs)),
                                    TraitParam::Equals(TyOrRe::Ty(result_ty)),
                                ]),
                            },
                        );
                    }

                    fallback_err.emit(&prim_fork);
                }

                tcx.intern(TyKind::Tuple(tcx.intern_list(&[])))
            }
            HirExprKind::Field(receiver, name) => {
                let receiver = self.check_expr(receiver, None).and_do(&mut divergence);

                if let Some(ty) = self.lookup_field(receiver, name) {
                    ty
                } else {
                    tcx.intern(TyKind::Error(
                        Diag::span_err(name.span, "no such field").emit(),
                    ))
                }
            }
            HirExprKind::Index(target, index) => {
                let target_ty = self.check_expr(target, None).and_do(&mut divergence);
                let index_ty = self.ccx_mut().fresh_ty_infer(
                    HrtbUniverse::ROOT,
                    InferTyVarSourceInfo::IndexInput {
                        span: index.r(s).span,
                    },
                );
                let output_ty = self.ccx_mut().fresh_ty_infer(
                    HrtbUniverse::ROOT,
                    InferTyVarSourceInfo::IndexOutput {
                        span: expr.r(s).span,
                    },
                );

                let index_trait = self.krate().r(s).lang_items.index_trait().unwrap();

                self.ccx_mut().oblige_ty_meets_trait_instantiated(
                    ClauseOrigin::root_report(ClauseOriginKind::Index {
                        target_span: target.r(s).span,
                        index_span: index.r(s).span,
                    }),
                    HrtbUniverse::ROOT,
                    target_ty,
                    TraitSpec {
                        def: index_trait,
                        params: tcx.intern_list(&[
                            TraitParam::Equals(TyOrRe::Ty(index_ty)),
                            TraitParam::Equals(TyOrRe::Ty(output_ty)),
                        ]),
                    },
                );

                self.check_expr_demand(index, index_ty)
                    .and_do(&mut divergence);

                output_ty
            }
            HirExprKind::Range(range_expr) => todo!(),
            HirExprKind::Local(local) => self.type_of_local(local),
            HirExprKind::AddrOf(mutability, pointee) => {
                let pointee = self.check_expr(pointee, None).and_do(&mut divergence);
                tcx.intern(TyKind::Reference(Re::Erased, mutability, pointee))
            }
            HirExprKind::Break { label, value } => {
                if label.kind.can_break_with_value() {
                    let demand = *self
                        .block_break_demands
                        .get_mut(&label)
                        .unwrap()
                        .get_or_insert_with(|| {
                            self.ccx.fresh_ty_infer(
                                HrtbUniverse::ROOT,
                                InferTyVarSourceInfo::LoopDemand {
                                    span: label.target.r(s).span,
                                },
                            )
                        });

                    self.check_expr_demand(value.unwrap(), demand).ignore();
                } else {
                    debug_assert!(value.is_none());
                }

                tcx.intern(TyKind::Simple(SimpleTyKind::Never))
            }
            HirExprKind::Continue(_label) => tcx.intern(TyKind::Simple(SimpleTyKind::Never)),
            HirExprKind::Return(rv) => {
                self.check_expr_demand(rv, self.return_ty).ignore();
                tcx.intern(TyKind::Simple(SimpleTyKind::Never))
            }
            HirExprKind::AdtCtorTy(spanned) => todo!(),
            HirExprKind::AdtCtorEnumVariant(obj, spanned) => todo!(),
            HirExprKind::Struct(hir_struct_expr) => todo!(),
            HirExprKind::Error(err) => tcx.intern(TyKind::Error(err)),
        };

        // Matches rustc behavior—we don't mark a subsequent expression as unreachable unless the
        // primitive `Never` type is returned.
        if let TyKind::Simple(SimpleTyKind::Never) =
            self.ccx_mut().peel_ty_infer_var_after_poll(ty).r(s)
        {
            divergence = Divergence::MustDiverge;
        }

        self.expr_types_pre_coerce.insert(expr, ty);

        TyAndDivergence::new(ty, divergence)
    }
}
