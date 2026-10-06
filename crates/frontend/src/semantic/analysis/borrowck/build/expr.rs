use crate::{
    base::arena::{HasListInterner as _, Obj},
    parse::ast::{AstBinOpKind, AstBoolLit, AstLit},
    semantic::{
        analysis::borrowck::build::{
            driver::{LabelledScope, MirFromThirCtx, MirRvalueOrPlace},
            scope::MirBuilderScopeIdx,
        },
        syntax::{
            MirAssignRvalue, MirBinOpKind, MirLocalIdx, MirOperand, MirPlace, MirPlaceElem,
            MirStmt, MirStmtKind, MirStmtSourceInfo, SigTy, ThirBlock, ThirBlockTrailing, ThirExpr,
            ThirExprKind, ThirStmt,
        },
    },
};

impl<'tcx> MirFromThirCtx<'tcx> {
    pub fn lower_expr_rvalue(
        &mut self,
        scope: MirBuilderScopeIdx,
        expr: Obj<ThirExpr>,
    ) -> MirAssignRvalue {
        let s = self.session();

        let rv = match self.lower_expr_preferred(scope, expr, None) {
            MirRvalueOrPlace::Rvalue(rvalue) => rvalue,
            MirRvalueOrPlace::Place(place) => {
                MirAssignRvalue::Use(self.builder.operand_mode(expr.r(s).ty).to_operand(place))
            }
        };

        if expr.r(s).causes_divergence(s) {
            self.builder.push_unreachable(scope);
        }

        rv
    }

    pub fn lower_expr_place(
        &mut self,
        scope: MirBuilderScopeIdx,
        expr: Obj<ThirExpr>,
        mut assign_into: Option<MirPlace>,
    ) -> MirPlace {
        let s = self.session();

        let rv = match self.lower_expr_preferred(scope, expr, assign_into) {
            MirRvalueOrPlace::Rvalue(rvalue) => {
                let assign_into =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                self.builder.push_statement(
                    scope,
                    MirStmt {
                        span: MirStmtSourceInfo::Simple(expr.r(s).span),
                        kind: MirStmtKind::Assign(Box::new((assign_into, rvalue))),
                    },
                );

                assign_into
            }
            MirRvalueOrPlace::Place(original_output) => {
                if let Some(assign_into) = assign_into
                    && original_output != assign_into
                {
                    self.builder.push_statement(
                        scope,
                        MirStmt {
                            span: MirStmtSourceInfo::Simple(expr.r(s).span),
                            kind: MirStmtKind::Assign(Box::new((
                                assign_into,
                                // The original output needs to be invalidated.
                                MirAssignRvalue::Use(MirOperand::Move(original_output)),
                            ))),
                        },
                    );
                }

                assign_into.unwrap_or(original_output)
            }
        };

        if expr.r(s).causes_divergence(s) {
            self.builder.push_unreachable(scope);
        }

        rv
    }

    pub fn lower_expr_operand(
        &mut self,
        scope: MirBuilderScopeIdx,
        expr: Obj<ThirExpr>,
    ) -> MirOperand {
        let s = self.session();
        let place = self.lower_expr_place(scope, expr, None);

        self.builder.operand_mode(expr.r(s).ty).to_operand(place)
    }

    pub fn lower_expr_operand_list(
        &mut self,
        scope: MirBuilderScopeIdx,
        expr: Obj<[Obj<ThirExpr>]>,
    ) -> Box<[MirOperand]> {
        let s = self.session();

        expr.r(s)
            .iter()
            .map(|&expr| self.lower_expr_operand(scope, expr))
            .collect()
    }

    // TODO: split up logical and temporary scopes
    pub fn lower_expr_preferred(
        &mut self,
        scope: MirBuilderScopeIdx,
        expr: Obj<ThirExpr>,
        mut assign_into: Option<MirPlace>,
    ) -> MirRvalueOrPlace {
        let tcx = self.tcx();
        let s = self.session();

        match *expr.r(s).kind {
            ThirExprKind::CreateZst => MirRvalueOrPlace::Rvalue(MirAssignRvalue::Zst(expr.r(s).ty)),
            ThirExprKind::CreateLiteral(lit) => {
                MirRvalueOrPlace::Rvalue(MirAssignRvalue::Literal(expr.r(s).ty, lit))
            }
            ThirExprKind::CreateTuple(elems) => MirRvalueOrPlace::Rvalue(MirAssignRvalue::Tuple(
                elems
                    .r(s)
                    .iter()
                    .map(|&elem| self.lower_expr_operand(scope, elem))
                    .collect(),
            )),
            ThirExprKind::PrimitiveBinOp(op, lhs, rhs) => match MirBinOpKind::from_ast(op) {
                MirBinOpKind::Straight(op) => MirRvalueOrPlace::Rvalue(MirAssignRvalue::BinaryOp(
                    op,
                    Box::new((
                        self.lower_expr_operand(scope, lhs),
                        self.lower_expr_operand(scope, rhs),
                    )),
                )),
                MirBinOpKind::Logical(op) => {
                    let assign_into = self.create_assign_into_place_if_needed(
                        scope,
                        &mut assign_into,
                        expr.r(s).ty,
                    );

                    let lhs = self.lower_expr_operand(scope, lhs);

                    let [short_scope, long_scope] = self.builder.push_switch_fixed(
                        scope,
                        lhs,
                        [op.short_circuit_if() as u64, !op.short_circuit_if() as u64],
                    );

                    self.builder.push_statement(
                        short_scope,
                        MirStmt {
                            span: MirStmtSourceInfo::Simple(expr.r(s).span),
                            kind: MirStmtKind::Assign(Box::new((
                                assign_into,
                                MirAssignRvalue::Literal(
                                    expr.r(s).ty,
                                    AstLit::Bool(AstBoolLit {
                                        span: expr.r(s).span,
                                        value: op.short_circuit_value(),
                                    }),
                                ),
                            ))),
                        },
                    );
                    self.builder.push_break(short_scope, short_scope);

                    self.lower_expr_place(long_scope, rhs, Some(assign_into));
                    self.builder.push_break(long_scope, long_scope);

                    MirRvalueOrPlace::Place(assign_into)
                }
            },
            ThirExprKind::PrimitiveUnOp(op, lhs) => {
                MirRvalueOrPlace::Rvalue(MirAssignRvalue::UnaryOp(
                    op,
                    MirOperand::Move(self.lower_expr_place(scope, lhs, None)),
                ))
            }
            ThirExprKind::NoOp(expr) => self.lower_expr_preferred(scope, expr, assign_into),
            ThirExprKind::Break(label, value) => {
                let label = self.labelled_scopes[&label];

                self.lower_expr_place(scope, value, Some(label.out_place));

                self.builder.push_break(scope, label.scope);

                MirRvalueOrPlace::Rvalue(MirAssignRvalue::UnreachablePlaceholder)
            }
            ThirExprKind::Continue(label) => {
                self.builder
                    .push_continue(scope, self.labelled_scopes[&label].scope);

                MirRvalueOrPlace::Rvalue(MirAssignRvalue::UnreachablePlaceholder)
            }
            ThirExprKind::Return(rv) => {
                let rv = self.lower_expr_rvalue(scope, rv);

                self.builder.push_statement(
                    scope,
                    MirStmt {
                        span: MirStmtSourceInfo::Simple(expr.r(s).span),
                        kind: MirStmtKind::Assign(Box::new((
                            MirPlace::new(tcx, MirLocalIdx::RETURN, []),
                            rv,
                        ))),
                    },
                );
                self.builder.push_return(scope);

                MirRvalueOrPlace::Rvalue(MirAssignRvalue::UnreachablePlaceholder)
            }
            ThirExprKind::Assign(lhs, rhs) => {
                let lhs = self.lower_expr_place(scope, lhs, None);
                let rhs = self.lower_expr_rvalue(scope, rhs);

                self.builder.push_statement(
                    scope,
                    MirStmt {
                        span: MirStmtSourceInfo::Simple(expr.r(s).span),
                        kind: MirStmtKind::Assign(Box::new((lhs, rhs))),
                    },
                );

                MirRvalueOrPlace::Rvalue(MirAssignRvalue::Tuple(Box::new([])))
            }
            ThirExprKind::Block(block) => {
                let out_place =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                let scope = self.builder.push_scope(scope);

                self.labelled_scopes
                    .insert(expr, LabelledScope { scope, out_place });

                self.lower_block(scope, block, Some(out_place));

                MirRvalueOrPlace::Place(out_place)
            }
            ThirExprKind::Loop(block) => {
                let out_place =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                self.labelled_scopes
                    .insert(expr, LabelledScope { scope, out_place });

                self.lower_block(scope, block, None);

                MirRvalueOrPlace::Place(out_place)
            }
            ThirExprKind::AddrOf(muta, target) => MirRvalueOrPlace::Rvalue(MirAssignRvalue::Ref(
                muta,
                self.lower_expr_place(scope, target, None),
            )),
            ThirExprKind::Call(callee, args) => {
                let destination =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                let callee = self.lower_expr_operand(scope, callee);
                let args = self.lower_expr_operand_list(scope, args);

                self.builder.push_call(scope, callee, args, destination);

                MirRvalueOrPlace::Place(destination)
            }
            ThirExprKind::Field(target, field) => MirRvalueOrPlace::Place(
                self.lower_expr_place(scope, target, None)
                    .extend(tcx, [MirPlaceElem::Field(field)]),
            ),
            ThirExprKind::CreateBracedAdt { ctor, fields, rest } => {
                todo!()
            }
            ThirExprKind::Local(local) => {
                MirRvalueOrPlace::Place(MirPlace::new(tcx, self.thir_locals[&local], []))
            }
            ThirExprKind::If {
                cond,
                truthy,
                falsy,
            } => {
                let assign_into =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                let [truthy_scope, falsy_scope] = self.lower_if_expr(scope, cond);

                self.lower_expr_place(truthy_scope, truthy, Some(assign_into));

                if let Some(falsy) = falsy {
                    self.lower_expr_place(falsy_scope, falsy, Some(assign_into));
                }

                self.builder.push_break(truthy_scope, truthy_scope);
                self.builder.push_break(falsy_scope, falsy_scope);

                MirRvalueOrPlace::Place(assign_into)
            }
            ThirExprKind::DynUse(site_idx, target) => {
                let target = self.lower_expr_operand(scope, target);

                MirRvalueOrPlace::Rvalue(MirAssignRvalue::DynUse(site_idx, target))
            }
            ThirExprKind::Match(scrutinee, arms) => {
                let out_place =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                self.lower_match(scope, scrutinee, arms, out_place);

                MirRvalueOrPlace::Place(out_place)
            }
            ThirExprKind::Let(_, _) => unreachable!(),
            ThirExprKind::Error(error) => MirRvalueOrPlace::Rvalue(MirAssignRvalue::Error(error)),
        }
    }

    pub fn lower_block(
        &mut self,
        scope: MirBuilderScopeIdx,
        expr: Obj<ThirBlock>,
        assign_into: Option<MirPlace>,
    ) {
        let s = self.session();

        for &stmt in &expr.r(s).stmts {
            match stmt {
                ThirStmt::Expr(expr) => {
                    let scope = self.builder.push_scope(scope);
                    let rvalue = self.lower_expr_rvalue(scope, expr);

                    self.builder.push_statement(
                        scope,
                        MirStmt {
                            span: MirStmtSourceInfo::Simple(expr.r(s).span),
                            kind: MirStmtKind::DiscardWithoutDrop(rvalue),
                        },
                    );
                }
                ThirStmt::Let(stmt) => {
                    self.lower_let_stmt(scope, stmt);
                }
            }
        }

        match (assign_into, expr.r(s).last_expr) {
            (None, ThirBlockTrailing::Present(_) | ThirBlockTrailing::MissingCoerceNever)
            | (Some(_), ThirBlockTrailing::MissingNotApplicable) => unreachable!(),

            (Some(place), ThirBlockTrailing::Present(last_expr)) => {
                self.lower_expr_place(scope, last_expr, Some(place));
            }
            (Some(_), ThirBlockTrailing::MissingCoerceNever) => {
                self.builder.push_unreachable(scope);
            }
            (None, ThirBlockTrailing::MissingNotApplicable) => {
                // (ignored)
            }
        }
    }

    pub fn lower_if_expr(
        &mut self,
        scope: MirBuilderScopeIdx,
        cond: Obj<ThirExpr>,
    ) -> [MirBuilderScopeIdx; 2] {
        let s = self.session();

        let mut cond = cond;

        // Constructs the following nested scopes...
        //
        // ```
        // 'break_after_truthy: {
        //     'break_if_falsy: {
        //         if !cond_1 {
        //             break 'break_if_falsy;
        //         }
        //
        //         if !cond_2 {
        //             break 'break_if_falsy;
        //         }
        //
        //         let binding;
        //         if !user pat logic {
        //             break 'break_if_falsy;
        //         }
        //
        //         'truthy_scope: {
        //             truthy logic;
        //             user break 'truthy_scope;
        //         }
        //
        //         break 'break_after_truthy;
        //     }
        //
        //     falsy logic;
        //     user break 'break_after_truthy;
        // }
        // ```
        let break_after_truthy = self.builder.push_scope(scope);
        let break_if_falsy = self.builder.push_scope(break_after_truthy);

        loop {
            if let ThirExprKind::PrimitiveBinOp(AstBinOpKind::And, lhs, rhs) = *cond.r(s).kind {
                match *lhs.r(s).kind {
                    ThirExprKind::Let(pat, scrutinee) => {
                        self.lower_let_expr(break_if_falsy, pat, scrutinee);
                    }
                    _ => {
                        let lhs = self.lower_expr_operand(break_if_falsy, lhs);

                        let [truthy, falsy] = self.builder.push_switch_fixed(scope, lhs, [1, 0]);
                        self.builder.push_break(truthy, truthy);
                        self.builder.push_break(falsy, break_if_falsy);
                    }
                }

                cond = rhs;
            } else {
                let lhs = self.lower_expr_operand(break_if_falsy, cond);

                let [truthy, falsy] = self.builder.push_switch_fixed(scope, lhs, [1, 0]);
                self.builder.push_break(truthy, truthy);
                self.builder.push_break(falsy, break_if_falsy);
                break;
            }
        }

        let truthy_scope = self.builder.push_scope(break_if_falsy);
        self.builder.push_break(break_if_falsy, break_after_truthy);

        [truthy_scope, break_if_falsy]
    }

    pub fn create_assign_into_place_if_needed(
        &mut self,
        scope: MirBuilderScopeIdx,
        place: &mut Option<MirPlace>,
        ty: SigTy,
    ) -> MirPlace {
        let tcx = self.tcx();

        *place.get_or_insert_with(|| MirPlace {
            local: self.builder.push_local(scope, ty),
            projections: tcx.intern_list(&[]),
        })
    }
}
