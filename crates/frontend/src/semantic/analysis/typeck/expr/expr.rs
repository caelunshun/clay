use crate::{
    base::{
        Diag,
        analysis::SpannedViewEncode as _,
        arena::{HasInterner as _, HasListInterner as _, Obj},
        syntax::HasSpan as _,
    },
    parse::ast::AstLit,
    semantic::{
        analysis::typeck::{
            BodyCtxt,
            infra::lookup::{LookupMethodResult, SpannedImportedAssocArgs},
        },
        infer::{HrtbUniverse, ObligeCause, ObligeCauseOrigin},
        lower::generics::normalize_positional_generic_arity_zip,
        syntax::{
            AdtInstance, Divergence, FnInstanceInner, HirBlock, HirExpr, HirExprKind,
            HirLabelledBlock, HirStmt, InferTyVarSourceInfo, LabelTargetKind, Re, RelationMode,
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

                        let ascription = self.ccx_mut().import_report_here(
                            HrtbUniverse::ROOT_REF,
                            import_env,
                            ascription,
                        );

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
            HirExprKind::Call(callee, actual_args) => {
                self.check_expr_inner_call(expr, callee, actual_args, &mut divergence)
            }
            HirExprKind::MethodCall {
                receiver,
                name,
                generics,
                args,
            } => self.check_expr_inner_method_call(receiver, name, generics, args, &mut divergence),
            HirExprKind::Tuple(children) => {
                let children = children
                    .r(s)
                    .iter()
                    .map(|&expr| self.check_expr(expr, None).and_do(&mut divergence))
                    .collect::<Vec<_>>();

                tcx.intern(TyKind::Tuple(tcx.intern_list(&children)))
            }
            HirExprKind::Binary(kind, lhs, rhs) => {
                self.check_expr_inner_bin_op(expr, kind, lhs, rhs, &mut divergence)
            }
            HirExprKind::Unary(kind, lhs) => {
                self.check_expr_inner_un_op(expr, kind, lhs, &mut divergence)
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

                let fn_ty = SpannedTyView::FnDef(
                    SpannedFnInstanceView {
                        owner: SpannedFnOwnerView::Item(def).encode(expr.r(s).span, tcx),
                        early_args,
                    }
                    .encode(expr.r(s).span, tcx),
                )
                .encode(expr.r(s).span, tcx);

                self.ccx_mut()
                    .import_report_here(HrtbUniverse::ROOT_REF, env, fn_ty)
            }
            HirExprKind::TypeRelative {
                self_ty,
                as_trait,
                assoc_name,
                assoc_args,
            } => 'res: {
                let env = self.import_env;

                let self_ty =
                    self.ccx_mut()
                        .import_report_here(HrtbUniverse::ROOT_REF, env, self_ty);

                let as_trait = as_trait.map(|as_trait| {
                    self.ccx_mut()
                        .importer()
                        .with_clause_applies_to(self_ty)
                        .import_report_here(HrtbUniverse::ROOT_REF, env, as_trait)
                });

                let mut arg_spans = None;
                let assoc_args = assoc_args.map(|assoc_args| {
                    let arg_spans = arg_spans.insert(
                        assoc_args
                            .iter(tcx)
                            .map(|v| v.own_span())
                            .collect::<Vec<_>>(),
                    );

                    SpannedImportedAssocArgs {
                        segment_span: assoc_args.own_span(),
                        arg_spans: arg_spans,
                        args: self.ccx_mut().import_report_here(
                            HrtbUniverse::ROOT_REF,
                            env,
                            assoc_args,
                        ),
                    }
                });

                let Some(resolution) =
                    self.lookup_type_relative(self_ty, as_trait, assoc_name, assoc_args)
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
                    .import_report_here(HrtbUniverse::ROOT_REF, env, as_ty);

                self.check_expr_demand(expr, as_ty).and_do(&mut divergence)
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
                    ObligeCause::new_report(ObligeCauseOrigin::HirBodyCheckForLoopIter {
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
                    kind: LabelTargetKind::Loop,
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
                    kind: LabelTargetKind::Block,
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
                        if !divergence.must_diverge() {
                            self.ccx_mut().oblige_ty_unifies_ty(
                                ObligeCause::new_report(
                                    ObligeCauseOrigin::HirBodyCheckReturnUnit {
                                        span: block.r(s).span,
                                    },
                                ),
                                demand,
                                tcx.intern(TyKind::Tuple(tcx.intern_list(&[]))),
                                RelationMode::Equate,
                            );
                        }

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
                self.check_expr_inner_assign_op(expr, kind, lhs, rhs, &mut divergence)
            }
            HirExprKind::Field(receiver, name) => {
                self.check_expr_inner_field(receiver, name, &mut divergence)
            }
            HirExprKind::Index(target, index) => {
                self.check_expr_inner_index(expr, target, index, &mut divergence)
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
