use crate::{
    base::{
        Diag,
        arena::{HasInterner as _, HasListInterner as _, Obj},
    },
    semantic::{
        analysis::typeck::BodyCtxt,
        infer::{
            ClauseFuel, ClauseImportEnv, FixArity, GenericSubst, HrtbUniverse, PrettyFmtOpts,
            SpannedError,
        },
        syntax::{
            AdtCtorFieldIdx, AdtCtorSyntax, AdtInstance, Divergence, DivergenceJoin, DynSiteIdx,
            FnInstanceInner, FnOwner, HirBlock, HirExpr, HirExprKind, HirLabelledBlock,
            HirMatchArm, HirRangeExpr, HirStmt, HirStructExpr, InferTyVarSourceInfo,
            LabelTargetKind, Re, RelationMode, SigAdtInstance, SimpleTyKind, ThirExprKind,
            ThirMatchArm, ThirStructField, TraitParam, TraitSpec, Ty, TyAndDivergence, TyKind,
            TyOrRe, UniversalTy, UniversalTyRootSourceInfo,
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

                        let ascription = self.ccx_mut().import_here(import_env, ascription);

                        if let Some(init) = stmt.r(s).init {
                            self.check_expr_demand(init, ascription).and_do(divergence);
                        }

                        ascription
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

                    self.check_pat_demand(stmt.r(s).pat, ascription, None);

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
        let import_env = self.import_env;

        let mut divergence = Divergence::MayDiverge;
        let res = match *expr.r(s).kind {
            HirExprKind::Array(elems) => {
                let elem = if elems.r(s).is_empty() {
                    self.ccx_mut().fresh_ty_infer(
                        HrtbUniverse::ROOT,
                        InferTyVarSourceInfo::EmptyArrayElem {
                            span: expr.r(s).span,
                        },
                    )
                } else {
                    self.check_exprs_equate(elems.r(s).iter().copied(), DivergenceJoin::Sequential)
                        .and_do(&mut divergence)
                };

                let vec_lang_item = self.krate().r(s).lang_items.vec().unwrap();

                let ty = tcx.intern(TyKind::Adt(AdtInstance {
                    def: vec_lang_item,
                    params: tcx.intern_list(&[TyOrRe::Ty(elem)]),
                }));

                self.put_thir_expr(expr, ty, move |bcx| {
                    ThirExprKind::CreateArray(bcx.confirm_thir_expr_list_post(elems))
                })
            }
            HirExprKind::Call(callee, actual_args) => {
                self.check_expr_inner_call(expr, callee, actual_args, &mut divergence)
            }
            HirExprKind::MethodCall {
                receiver,
                name,
                generics,
                args,
            } => self.check_expr_inner_method_call(
                expr,
                receiver,
                name,
                generics,
                args,
                &mut divergence,
            ),
            HirExprKind::Tuple(children_exprs) => {
                let children = children_exprs
                    .r(s)
                    .iter()
                    .map(|&expr| self.check_expr(expr, None).and_do(&mut divergence))
                    .collect::<Vec<_>>();

                let ty = tcx.intern(TyKind::Tuple(tcx.intern_list(&children)));

                self.put_thir_expr(expr, ty, move |bcx| {
                    ThirExprKind::CreateTuple(bcx.confirm_thir_expr_list_post(children_exprs))
                })
            }
            HirExprKind::Binary(kind, lhs, rhs) => {
                self.check_expr_inner_bin_op(expr, kind, lhs, rhs, &mut divergence)
            }
            HirExprKind::Unary(kind, lhs) => {
                self.check_expr_inner_un_op(expr, kind, lhs, &mut divergence)
            }
            HirExprKind::Literal(lit) => self.check_expr_inner_lit(expr, lit),
            HirExprKind::FnItemLit(def, early_args) => {
                let env = self.import_env;

                let ty = tcx.intern(TyKind::FnDef(
                    self.ccx_mut()
                        .importer_here(env)
                        .import_fn_instance_from_owner(
                            FnOwner::Item(def),
                            early_args,
                            FixArity::AssumeCorrect,
                        )
                        .report_loud(),
                ));

                self.put_thir_expr(expr, ty, |_bcx| ThirExprKind::CreateZst)
            }
            HirExprKind::TypeRelative {
                self_ty,
                as_trait,
                assoc_name,
                assoc_args,
            } => 'res: {
                let env = self.import_env;

                let self_ty = self.ccx_mut().import_here(env, self_ty);

                let as_trait = as_trait.map(|as_trait| self.ccx_mut().import_here(env, as_trait));

                let Some(resolution) =
                    self.lookup_type_relative(self_ty, as_trait, assoc_name, assoc_args)
                else {
                    break 'res self.put_thir_expr_err(
                        expr,
                        Diag::span_err(assoc_name.span, "not found").emit(),
                    );
                };

                self.put_thir_expr(expr, resolution, |_bcx| ThirExprKind::CreateZst)
            }
            HirExprKind::Cast(target, as_ty) => {
                let env = self.import_env;
                let as_ty = self.ccx_mut().import_here(env, as_ty);

                let ty = self
                    .check_expr_demand(target, as_ty)
                    .and_do(&mut divergence);

                self.put_thir_expr(expr, ty, move |bcx| {
                    ThirExprKind::NoOp(bcx.confirm_thir_expr_post(target))
                })
            }
            HirExprKind::Use(target) => {
                let inner_ty = self.check_expr(target, None).and_do(&mut divergence);
                let inner_ty = self.ccx_mut().peel_ty_infer_var_after_poll(inner_ty);

                // TODO: allocate these and confirm them so we can do analysis in MIR.
                let site = DynSiteIdx::from_raw(0);

                match *inner_ty.r(s) {
                    TyKind::Trait(lt, muta, clauses) => {
                        let universal =
                            UniversalTy::Root(self.ccx_mut().fresh_ty_universal_root_idx(
                                HrtbUniverse::ROOT,
                                UniversalTyRootSourceInfo::UsedDyn {
                                    span: target.r(s).span,
                                    site,
                                },
                            ));

                        self.ccx_mut()
                            .init_ty_universal_direct_clauses(universal, clauses);

                        let ty = tcx.intern(TyKind::Reference(
                            lt,
                            muta,
                            tcx.intern(TyKind::Universal(universal)),
                        ));

                        self.put_thir_expr(expr, ty, move |bcx| {
                            ThirExprKind::DynUse(site, bcx.confirm_thir_expr_post(target))
                        })
                    }
                    TyKind::Error(err) => self.put_thir_expr_err(expr, err),
                    _ => self.put_thir_expr_err(
                        expr,
                        Diag::span_err(
                            target.r(s).span,
                            format_args!(
                                "expected `dyn Trait`-object, got `{}`",
                                self.ccx().pretty(PrettyFmtOpts::default()).wrap(inner_ty)
                            ),
                        )
                        .emit(),
                    ),
                }
            }
            HirExprKind::If {
                cond,
                truthy,
                falsy,
            } => {
                self.check_expr_demand(cond, tcx.intern(TyKind::Simple(SimpleTyKind::Bool)))
                    .and_do(&mut divergence);

                // TODO: Flatten
                let ty = self
                    .check_exprs_equate(
                        [Some(truthy), falsy].into_iter().flatten(),
                        DivergenceJoin::Choice,
                    )
                    .and_do(&mut divergence);

                self.put_thir_expr(expr, ty, move |bcx| ThirExprKind::If {
                    cond: bcx.confirm_thir_expr_post(cond),
                    truthy: bcx.confirm_thir_expr_post(truthy),
                    falsy: bcx.confirm_opt_thir_expr_post(falsy),
                })
            }
            HirExprKind::While(cond, block) => {
                self.check_expr_demand(cond, tcx.intern(TyKind::Simple(SimpleTyKind::Bool)))
                    .and_do(&mut divergence);

                self.check_block_with_no_final_expr(block);

                let ty = tcx.intern(TyKind::Tuple(tcx.intern_list(&[])));

                self.put_thir_expr(expr, ty, move |bcx| {
                    ThirExprKind::While(
                        bcx.confirm_thir_expr_post(cond),
                        bcx.confirm_thir_block_uncached(block, ty),
                    )
                })
            }
            HirExprKind::Let(pat, scrutinee_expr) => {
                let scrutinee = self
                    .check_expr(scrutinee_expr, None)
                    .and_do(&mut divergence);
                self.check_pat_demand(pat, scrutinee, None);

                let ty = tcx.intern(TyKind::Simple(SimpleTyKind::Bool));

                self.put_thir_expr(expr, ty, move |bcx| {
                    ThirExprKind::Let(
                        bcx.confirm_thir_pat_outer(pat),
                        bcx.confirm_thir_expr_post(scrutinee_expr),
                    )
                })
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

                self.ccx_mut()
                    .oblige_ty_meets_trait_instantiated(
                        ClauseFuel::new(),
                        HrtbUniverse::ROOT,
                        iter_ty,
                        TraitSpec {
                            def: into_iter_trait,
                            params: tcx.intern_list(&[
                                TraitParam::Unspecified(tcx.intern_list(&[])),
                                TraitParam::Equals(TyOrRe::Ty(elem_ty)),
                            ]),
                        },
                    )
                    // TODO
                    .map({
                        let span = iter.r(s).span;
                        move |_ccx, error| SpannedError(span, error)
                    })
                    .report_loud();

                self.check_pat_demand(pat, elem_ty, None);

                self.check_block_with_no_final_expr(body);

                let ty = tcx.intern(TyKind::Tuple(tcx.intern_list(&[])));

                self.put_thir_expr(expr, ty, |bcx| todo!())
            }
            HirExprKind::Loop(block) => {
                let label = HirLabelledBlock {
                    target: expr,
                    kind: LabelTargetKind::Loop,
                };

                self.block_break_demands.insert(label, None);
                self.check_block_with_no_final_expr(block);

                let ty = if let Some(break_ty) = self.block_break_demands[&label] {
                    break_ty
                } else {
                    tcx.intern(TyKind::Simple(SimpleTyKind::Never))
                };

                self.put_thir_expr(expr, ty, move |bcx| {
                    let tcx = bcx.tcx();

                    ThirExprKind::Loop(bcx.confirm_thir_block_uncached(
                        block,
                        tcx.intern(TyKind::Tuple(tcx.intern_list(&[]))),
                    ))
                })
            }
            HirExprKind::Match(scrutinee_expr, arms) => {
                let scrutinee = self
                    .check_expr(scrutinee_expr, None)
                    .and_do(&mut divergence);

                let arm_demand = demand_hint.unwrap_or_else(|| {
                    self.ccx_mut().fresh_ty_infer(
                        HrtbUniverse::ROOT,
                        InferTyVarSourceInfo::HoleInfer {
                            span: expr.r(s).span,
                        },
                    )
                });

                let mut body_divergence = Divergence::MustDiverge;

                for &arm in arms.r(s) {
                    let HirMatchArm {
                        span: _,
                        pat,
                        guard,
                        body,
                    } = *arm.r(s);

                    let mut arm_divergence = Divergence::MayDiverge;

                    self.check_pat_demand(pat, scrutinee, None);

                    if let Some(guard) = guard {
                        self.check_expr_demand(
                            guard,
                            tcx.intern(TyKind::Simple(SimpleTyKind::Bool)),
                        )
                        .and_do(&mut arm_divergence);
                    }

                    self.check_expr_demand(body, arm_demand)
                        .and_do(&mut arm_divergence);

                    body_divergence |= arm_divergence;
                }

                divergence &= body_divergence;

                self.put_thir_expr(expr, arm_demand, move |bcx| {
                    let s = bcx.session();

                    ThirExprKind::Match(
                        bcx.confirm_thir_expr_post(scrutinee_expr),
                        Obj::new_iter(
                            arms.r(s).iter().map(|arm| {
                                let arm = arm.r(s);

                                ThirMatchArm {
                                    span: arm.span,
                                    pat: bcx.confirm_thir_pat_outer(arm.pat),
                                    guard: bcx.confirm_opt_thir_expr_post(arm.guard),
                                    body: bcx.confirm_thir_expr_post(arm.body),
                                }
                            }),
                            s,
                        ),
                    )
                })
            }
            HirExprKind::Block(block) => {
                let label = HirLabelledBlock {
                    target: expr,
                    kind: LabelTargetKind::Block,
                };

                self.block_break_demands.insert(label, demand_hint);
                self.check_block_stmts(&block.r(s).stmts, &mut divergence);

                let ty = if let Some(last_expr) = block.r(s).last_expr {
                    if let Some(demand) = self.block_break_demands[&label] {
                        self.check_expr_demand(last_expr, demand)
                            .and_do(&mut divergence)
                    } else {
                        self.check_expr(last_expr, demand_hint)
                            .and_do(&mut divergence)
                    }
                } else {
                    if let Some(demand) = self.block_break_demands[&label] {
                        if !divergence.must_diverge() {
                            self.ccx_mut()
                                .oblige_ty_unifies_ty(
                                    demand,
                                    tcx.intern(TyKind::Tuple(tcx.intern_list(&[]))),
                                    RelationMode::Equate,
                                )
                                // TODO
                                .map({
                                    let span = block.r(s).span;
                                    move |_ccx, error| SpannedError(span, error)
                                })
                                .report_loud();
                        }

                        demand
                    } else if divergence.must_diverge() {
                        tcx.intern(TyKind::Simple(SimpleTyKind::Never))
                    } else {
                        tcx.intern(TyKind::Tuple(tcx.intern_list(&[])))
                    }
                };

                self.put_thir_expr(expr, ty, move |bcx| {
                    ThirExprKind::Block(bcx.confirm_thir_block_uncached(block, ty))
                })
            }
            HirExprKind::Assign(pat, rhs) => {
                self.check_expr_inner_assign(expr, pat, rhs, &mut divergence)
            }
            HirExprKind::AssignOp(kind, lhs, rhs) => {
                self.check_expr_inner_assign_op(expr, kind, lhs, rhs, &mut divergence)
            }
            HirExprKind::Field(receiver, name) => {
                self.check_expr_inner_field(expr, receiver, name, &mut divergence)
            }
            HirExprKind::Index(target, index) => {
                self.check_expr_inner_index(expr, target, index, &mut divergence)
            }
            HirExprKind::Range(
                inner @ HirRangeExpr {
                    low,
                    high,
                    limits: _,
                },
            ) => {
                let res = self.check_range_expr(inner).and_do(&mut divergence);
                let ty = res.range_ty(self);

                self.put_thir_expr(expr, ty, move |bcx| {
                    let s = bcx.session();

                    let ctor = *res
                        .lang_item(&bcx.krate().r(s).lang_items)
                        .r(s)
                        .kind
                        .as_struct()
                        .unwrap()
                        .r(s)
                        .ctor;

                    let fields = [
                        bcx.confirm_opt_thir_expr_post(low),
                        bcx.confirm_opt_thir_expr_post(high),
                    ]
                    .into_iter()
                    .filter_map(|v| v)
                    .enumerate()
                    .map(|(idx, expr)| ThirStructField {
                        span: expr.r(s).span,
                        idx: AdtCtorFieldIdx::from_usize(idx),
                        init: expr,
                    })
                    .collect::<Vec<_>>();

                    ThirExprKind::CreateBracedAdt {
                        ctor,
                        fields: Obj::new_iter(fields, s),
                        rest: None,
                    }
                })
            }
            HirExprKind::Local(local) => {
                let ty = self.type_of_local(local);

                self.put_thir_expr(expr, ty, move |bcx| {
                    ThirExprKind::Local(bcx.confirm_thir_local(local))
                })
            }
            HirExprKind::AddrOf(mutability, pointee_expr) => {
                let pointee = self.check_expr(pointee_expr, None).and_do(&mut divergence);
                let ty = tcx.intern(TyKind::Reference(Re::ERASED, mutability, pointee));

                self.put_thir_expr(expr, ty, move |bcx| {
                    ThirExprKind::AddrOf(mutability, bcx.confirm_thir_expr_post(pointee_expr))
                })
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

                    self.check_expr_demand(value.unwrap(), demand)
                        .ignore_divergence();
                } else {
                    debug_assert!(value.is_none());
                }

                let ty = tcx.intern(TyKind::Simple(SimpleTyKind::Never));

                self.put_thir_expr(expr, ty, move |bcx| {
                    ThirExprKind::Break(
                        bcx.confirm_thir_label(label),
                        bcx.confirm_opt_thir_expr_post(value),
                    )
                })
            }
            HirExprKind::Continue(label) => {
                let ty = tcx.intern(TyKind::Simple(SimpleTyKind::Never));

                self.put_thir_expr(expr, ty, move |bcx| {
                    ThirExprKind::Continue(bcx.confirm_thir_label(label))
                })
            }
            HirExprKind::Return(rv) => {
                self.check_expr_demand(rv, self.return_ty)
                    .ignore_divergence();

                let ty = tcx.intern(TyKind::Simple(SimpleTyKind::Never));

                self.put_thir_expr(expr, ty, move |bcx| {
                    ThirExprKind::Return(bcx.confirm_thir_expr_post(rv))
                })
            }
            HirExprKind::AdtCtorTy(ty) => 'check: {
                let ty_span = ty.r(s).span;
                let ty = self.ccx_mut().import_here(import_env, ty);

                let ctor = match self.resolve_ty_as_adt_ctor_instance(ty_span, ty) {
                    Ok(v) => v,
                    Err(err) => {
                        break 'check self.put_thir_expr_err(expr, err);
                    }
                };

                let ty = match &ctor.def.r(s).syntax {
                    AdtCtorSyntax::Unit => ctor.to_adt_instance_ty(tcx),
                    AdtCtorSyntax::Tuple => {
                        _ = self.check_tuple_ctor_visibilities(ty_span, ctor);

                        tcx.intern(TyKind::FnDef(tcx.intern(FnInstanceInner {
                            owner: FnOwner::AdtCtor(ctor.def),
                            early_args: Some(ctor.params),
                        })))
                    }
                    AdtCtorSyntax::Named(_) => {
                        break 'check self.put_thir_expr_err(
                            expr,
                            Diag::span_err(
                                ty_span,
                                "cannot create functions out of braced constructors",
                            )
                            .emit(),
                        );
                    }
                };

                self.put_thir_expr(expr, ty, |_bcx| ThirExprKind::CreateZst)
            }
            HirExprKind::AdtCtorEnumVariant(item, params) => {
                let ctor = *item.r(s).adt_variant(s).r(s).ctor;

                let ty = match &ctor.r(s).syntax {
                    AdtCtorSyntax::Unit => {
                        let AdtInstance { def: _, params } = self.ccx_mut().import_here(
                            import_env,
                            SigAdtInstance {
                                def: item.r(s).adt(s),
                                params,
                            },
                        );

                        tcx.intern(TyKind::Adt(AdtInstance {
                            def: ctor.r(s).owner.item(s),
                            params,
                        }))
                    }
                    AdtCtorSyntax::Tuple => {
                        let AdtInstance { def: _, params } = self.ccx_mut().import_here(
                            import_env,
                            SigAdtInstance {
                                def: item.r(s).adt(s),
                                params,
                            },
                        );

                        tcx.intern(TyKind::FnDef(tcx.intern(FnInstanceInner {
                            owner: FnOwner::AdtCtor(ctor),
                            early_args: Some(params),
                        })))
                    }
                    AdtCtorSyntax::Named(_) => tcx.intern(TyKind::Error(
                        Diag::span_err(
                            expr.r(s).span,
                            "cannot create functions out of braced constructors",
                        )
                        .emit(),
                    )),
                };

                self.put_thir_expr(expr, ty, |_bcx| ThirExprKind::CreateZst)
            }
            HirExprKind::Struct(HirStructExpr {
                ctor_span,
                ctor,
                fields,
                rest,
            }) => 'check: {
                let ctor = match self.resolve_adt_ctor(ctor_span, ctor) {
                    Ok(v) => v,
                    Err(err) => break 'check self.put_thir_expr_err(expr, err),
                };

                match &ctor.def.r(s).syntax {
                    AdtCtorSyntax::Unit | AdtCtorSyntax::Tuple => {
                        break 'check self.put_thir_expr_err(
                            expr,
                            Diag::span_err(
                                ctor_span,
                                "cannot use braced initializer for non-braced ADT constructor",
                            )
                            .emit(),
                        );
                    }
                    AdtCtorSyntax::Named(_) => {
                        // (fallthrough)
                    }
                }

                let instance_owner = ctor.def.r(s).owner.item(s);
                let instance_ty = self.adt_ctor_to_instance_ty(ctor);

                let mapping = self.match_up_ctor_members(
                    ctor.def,
                    fields
                        .r(s)
                        .iter()
                        .enumerate()
                        .map(|(idx, field)| (field.name, idx))
                        .collect::<Vec<_>>(),
                    /* deny_missing */ rest.is_none().then_some(ctor_span),
                );

                for &(adt_ctor_field, idx_in_expr) in &mapping {
                    let init_expr = fields.r(s)[idx_in_expr].init;

                    let init_ty_orig = *ctor.def.r(s).fields[adt_ctor_field].ty;
                    let init_ty_env = ClauseImportEnv::new(
                        Some(instance_ty),
                        [GenericSubst::new(instance_owner.r(s).generics, ctor.params)],
                    );

                    let init_ty = self.ccx_mut().import_elsewhere(&init_ty_env, init_ty_orig);

                    // Mapping follows evaluation order with some filtering for unmatched fields.
                    self.check_expr_demand(init_expr, init_ty)
                        .and_do(&mut divergence);
                }

                if let Some(rest) = rest {
                    self.check_expr_demand(rest, instance_ty)
                        .and_do(&mut divergence);
                }

                self.put_thir_expr(expr, instance_ty, move |bcx| {
                    let s = bcx.session();

                    ThirExprKind::CreateBracedAdt {
                        ctor: ctor.def,
                        fields: Obj::new_iter(
                            mapping.into_iter().map(|(resolved_idx, expr_idx)| {
                                let field = fields.r(s)[expr_idx];

                                ThirStructField {
                                    span: field.name.span,
                                    idx: resolved_idx,
                                    init: bcx.confirm_thir_expr_post(field.init),
                                }
                            }),
                            s,
                        ),
                        rest: bcx.confirm_opt_thir_expr_post(rest),
                    }
                })
            }
            HirExprKind::Error(err) => self.put_thir_expr_err(expr, err),
        };

        assert_eq!(res.expr, expr);

        // Matches rustc behavior—we don't mark a subsequent expression as unreachable unless the
        // primitive `Never` type is returned.
        if let TyKind::Simple(SimpleTyKind::Never) =
            self.ccx_mut().peel_ty_infer_var_after_poll(res.ty).r(s)
        {
            divergence = Divergence::MustDiverge;
        }

        TyAndDivergence::new(res.ty, divergence)
    }
}
