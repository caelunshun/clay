use crate::{
    base::arena::{HasListInterner as _, Obj},
    parse::ast::{AstBinOpKind, AstBoolLit, AstLit},
    semantic::{
        analysis::borrowck::build::{
            driver::{LabelledScope, MirFromThirCtx, MirRvalueOrPlace},
            scope::{IfKind, MirScopedBuilder as _},
        },
        syntax::{
            MirBinOpKind, MirLocal, MirLocalIdx, MirOperand, MirPlace, MirPlaceElem, MirRvalue,
            MirScopeIdx, MirSourceInfo, ResolvedFieldIdx, SigTy, ThirBlock, ThirBlockTrailing,
            ThirExpr, ThirExprKind, ThirStmt,
        },
    },
};

impl<'tcx> MirFromThirCtx<'tcx> {
    pub fn lower_expr_rvalue(&mut self, scope: MirScopeIdx, expr: Obj<ThirExpr>) -> MirRvalue {
        let s = self.session();

        let rv = match self.lower_expr_preferred(scope, expr, None) {
            MirRvalueOrPlace::Rvalue(rvalue) => rvalue,
            MirRvalueOrPlace::Place(place) => MirRvalue::Use(
                self.trait_cache
                    .operand_mode(expr.r(s).ty)
                    .to_operand(place),
            ),
        };

        if expr.r(s).causes_divergence(s) {
            self.push_unreachable(scope, MirSourceInfo::ExprDivergent);
        }

        rv
    }

    pub fn lower_expr_place(
        &mut self,
        scope: MirScopeIdx,
        expr: Obj<ThirExpr>,
        mut assign_into: Option<MirPlace>,
    ) -> MirPlace {
        let s = self.session();

        let rv = match self.lower_expr_preferred(scope, expr, assign_into) {
            MirRvalueOrPlace::Rvalue(rvalue) => {
                let assign_into =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                self.push_assign(
                    scope,
                    MirSourceInfo::Simple(expr.r(s).span),
                    assign_into,
                    rvalue,
                );

                assign_into
            }
            MirRvalueOrPlace::Place(original_output) => {
                if let Some(assign_into) = assign_into
                    && original_output != assign_into
                {
                    self.push_assign(
                        scope,
                        MirSourceInfo::Simple(expr.r(s).span),
                        assign_into,
                        // The original output needs to be invalidated.
                        MirRvalue::Use(MirOperand::Move(original_output)),
                    );
                }

                assign_into.unwrap_or(original_output)
            }
        };

        if expr.r(s).causes_divergence(s) {
            self.push_unreachable(scope, MirSourceInfo::ExprDivergent);
        }

        rv
    }

    pub fn lower_expr_operand(&mut self, scope: MirScopeIdx, expr: Obj<ThirExpr>) -> MirOperand {
        let s = self.session();
        let place = self.lower_expr_place(scope, expr, None);

        self.trait_cache
            .operand_mode(expr.r(s).ty)
            .to_operand(place)
    }

    pub fn lower_expr_operand_list(
        &mut self,
        scope: MirScopeIdx,
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
        scope: MirScopeIdx,
        expr: Obj<ThirExpr>,
        mut assign_into: Option<MirPlace>,
    ) -> MirRvalueOrPlace {
        let tcx = self.tcx();
        let s = self.session();

        match *expr.r(s).kind {
            ThirExprKind::CreateZst => MirRvalueOrPlace::Rvalue(MirRvalue::Zst(expr.r(s).ty)),
            ThirExprKind::CreateLiteral(lit) => {
                MirRvalueOrPlace::Rvalue(MirRvalue::Literal(expr.r(s).ty, lit))
            }
            ThirExprKind::CreateTuple(elems) => MirRvalueOrPlace::Rvalue(MirRvalue::Tuple(
                elems
                    .r(s)
                    .iter()
                    .map(|&elem| self.lower_expr_operand(scope, elem))
                    .collect(),
            )),
            ThirExprKind::PrimitiveBinOp(op, lhs, rhs) => match MirBinOpKind::from_ast(op) {
                MirBinOpKind::Straight(op) => MirRvalueOrPlace::Rvalue(MirRvalue::BinaryOp(
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

                    self.push_if_else(
                        scope,
                        MirSourceInfo::Todo,
                        lhs,
                        IfKind::trigger_on(op.short_circuit_if()),
                        |this, short_circuit| {
                            this.push_assign(
                                short_circuit,
                                MirSourceInfo::Todo,
                                assign_into,
                                MirRvalue::Literal(
                                    expr.r(s).ty,
                                    AstLit::Bool(AstBoolLit {
                                        span: expr.r(s).span,
                                        value: op.short_circuit_value(),
                                    }),
                                ),
                            );
                        },
                        |this, long_circuit| {
                            this.lower_expr_place(long_circuit, rhs, Some(assign_into));
                        },
                    );

                    MirRvalueOrPlace::Place(assign_into)
                }
            },
            ThirExprKind::PrimitiveUnOp(op, lhs) => MirRvalueOrPlace::Rvalue(MirRvalue::UnaryOp(
                op,
                MirOperand::Move(self.lower_expr_place(scope, lhs, None)),
            )),
            ThirExprKind::NoOp(expr) => self.lower_expr_preferred(scope, expr, assign_into),
            ThirExprKind::Break(label, value) => {
                let label = self.labelled_scopes[&label];

                self.lower_expr_place(scope, value, Some(label.out_place));

                self.push_break(scope, MirSourceInfo::Todo, label.scope);

                MirRvalueOrPlace::Rvalue(MirRvalue::UnreachablePlaceholder)
            }
            ThirExprKind::Continue(label) => {
                self.push_continue(
                    scope,
                    MirSourceInfo::Todo,
                    self.labelled_scopes[&label].scope,
                );

                MirRvalueOrPlace::Rvalue(MirRvalue::UnreachablePlaceholder)
            }
            ThirExprKind::Return(rv) => {
                let rv = self.lower_expr_rvalue(scope, rv);

                self.push_assign(
                    scope,
                    MirSourceInfo::Todo,
                    MirPlace::new(tcx, MirLocalIdx::RETURN, []),
                    rv,
                );
                self.push_return(scope, MirSourceInfo::Todo);

                MirRvalueOrPlace::Rvalue(MirRvalue::UnreachablePlaceholder)
            }
            ThirExprKind::Assign(lhs, rhs) => {
                let lhs = self.lower_expr_place(scope, lhs, None);
                let rhs = self.lower_expr_rvalue(scope, rhs);

                self.push_assign(scope, MirSourceInfo::Simple(expr.r(s).span), lhs, rhs);

                MirRvalueOrPlace::Rvalue(MirRvalue::Tuple(Box::new([])))
            }
            ThirExprKind::Block(block) => {
                let out_place =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                self.push_scope(scope, MirSourceInfo::Todo, |this, scope| {
                    this.labelled_scopes
                        .insert(expr, LabelledScope { scope, out_place });

                    this.lower_block_flat(scope, block, None);

                    this.labelled_scopes.remove(&expr);
                });

                MirRvalueOrPlace::Place(out_place)
            }
            ThirExprKind::Loop(block) => {
                let out_place =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                self.push_loop(scope, MirSourceInfo::Todo, |this, scope| {
                    this.labelled_scopes
                        .insert(expr, LabelledScope { scope, out_place });

                    this.lower_block_flat(scope, block, None);

                    this.labelled_scopes.remove(&expr);
                });

                MirRvalueOrPlace::Place(out_place)
            }
            ThirExprKind::AddrOf(muta, target) => MirRvalueOrPlace::Rvalue(MirRvalue::Ref(
                muta,
                self.lower_expr_place(scope, target, None),
            )),
            ThirExprKind::Call(callee, args) => {
                let destination =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                let callee = self.lower_expr_operand(scope, callee);
                let args = self.lower_expr_operand_list(scope, args);

                self.push_call(scope, MirSourceInfo::Todo, destination, callee, args);

                MirRvalueOrPlace::Place(destination)
            }
            ThirExprKind::Field(target, field) => MirRvalueOrPlace::Place(
                self.lower_expr_place(scope, target, None)
                    .extend(tcx, [MirPlaceElem::Field(field)]),
            ),
            ThirExprKind::CreateBracedAdt { ctor, fields, rest } => {
                if let Some(rest) = rest {
                    let output = self.create_assign_into_place_if_needed(
                        scope,
                        &mut assign_into,
                        expr.r(s).ty,
                    );

                    self.lower_expr_place(scope, rest, Some(output));

                    for &field in fields.r(s) {
                        self.lower_expr_place(
                            scope,
                            field.init,
                            Some(output.extend(
                                tcx,
                                [MirPlaceElem::Field(ResolvedFieldIdx::Adt(ctor, field.idx))],
                            )),
                        );
                    }

                    MirRvalueOrPlace::Place(output)
                } else {
                    let mut field_places = (0..ctor.r(s).fields.len())
                        .map(|_| None)
                        .collect::<Box<[_]>>();

                    for &field in fields.r(s) {
                        field_places[field.idx.index()] =
                            Some(self.lower_expr_operand(scope, field.init))
                    }

                    MirRvalueOrPlace::Rvalue(MirRvalue::Adt(
                        ctor,
                        field_places.into_iter().map(|v| v.unwrap()).collect(),
                    ))
                }
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

                self.lower_if_expr(
                    scope,
                    cond,
                    |this, scope| {
                        this.lower_expr_place(scope, truthy, Some(assign_into));
                    },
                    falsy.map(|falsy| {
                        move |this: &mut MirFromThirCtx<'tcx>, scope| {
                            this.lower_expr_place(scope, falsy, Some(assign_into));
                        }
                    }),
                );

                MirRvalueOrPlace::Place(assign_into)
            }
            ThirExprKind::DynUse(site_idx, target) => {
                let target = self.lower_expr_operand(scope, target);

                MirRvalueOrPlace::Rvalue(MirRvalue::DynUse(site_idx, target))
            }
            ThirExprKind::Match(scrutinee, arms) => {
                let out_place =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                self.lower_match(scope, scrutinee, arms, out_place);

                MirRvalueOrPlace::Place(out_place)
            }
            ThirExprKind::Let(_, _) => unreachable!(),
            ThirExprKind::Error(error) => MirRvalueOrPlace::Rvalue(MirRvalue::Error(error)),
        }
    }

    pub fn lower_block_flat(
        &mut self,
        scope: MirScopeIdx,
        block: Obj<ThirBlock>,
        assign_into: Option<MirPlace>,
    ) {
        let s = self.session();

        for &stmt in &block.r(s).stmts {
            match stmt {
                ThirStmt::Expr(expr) => {
                    self.push_scope(scope, MirSourceInfo::Todo, |this, scope| {
                        // Dropped by leaving the scope.
                        this.lower_expr_place(scope, expr, None);
                    });
                }
                ThirStmt::Let(stmt) => {
                    self.lower_let_stmt(scope, stmt);
                }
            }
        }

        match (assign_into, block.r(s).last_expr) {
            (None, ThirBlockTrailing::Present(_) | ThirBlockTrailing::MissingCoerceNever)
            | (Some(_), ThirBlockTrailing::MissingNotApplicable) => unreachable!(),

            (Some(place), ThirBlockTrailing::Present(last_expr)) => {
                self.lower_expr_place(scope, last_expr, Some(place));
            }
            (Some(_), ThirBlockTrailing::MissingCoerceNever) => {
                self.push_unreachable(scope, MirSourceInfo::ExprDivergent);
            }
            (None, ThirBlockTrailing::MissingNotApplicable) => {
                // (ignored)
            }
        }
    }

    pub fn lower_if_expr(
        &mut self,
        scope: MirScopeIdx,
        cond: Obj<ThirExpr>,
        if_truthy: impl FnOnce(&mut Self, MirScopeIdx),
        if_falsy: Option<impl FnOnce(&mut Self, MirScopeIdx)>,
    ) {
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
        self.push_scope(scope, MirSourceInfo::Todo, |this, break_after_truthy| {
            this.push_scope(
                break_after_truthy,
                MirSourceInfo::Todo,
                |this, break_if_falsy| {
                    let lower_cond = |this: &mut MirFromThirCtx<'tcx>, cond: Obj<ThirExpr>| {
                        let cond = this.lower_expr_operand(break_if_falsy, cond);

                        this.push_if(
                            break_if_falsy,
                            MirSourceInfo::Todo,
                            cond,
                            IfKind::IfFalse,
                            |this, cond_falsy| {
                                this.push_break(cond_falsy, MirSourceInfo::Todo, break_if_falsy);
                            },
                        );
                    };

                    loop {
                        if let ThirExprKind::PrimitiveBinOp(AstBinOpKind::And, lhs, rhs) =
                            *cond.r(s).kind
                        {
                            match *lhs.r(s).kind {
                                ThirExprKind::Let(pat, scrutinee) => {
                                    this.lower_let_expr(break_if_falsy, pat, scrutinee);
                                }
                                _ => {
                                    lower_cond(this, lhs);
                                }
                            }

                            cond = rhs;
                        } else {
                            lower_cond(this, cond);
                            break;
                        }
                    }

                    if_truthy(this, break_if_falsy);
                    this.push_break(break_if_falsy, MirSourceInfo::Todo, break_after_truthy);
                },
            );

            if let Some(if_falsy) = if_falsy {
                if_falsy(this, break_after_truthy);
            }
        });
    }

    pub fn create_assign_into_place_if_needed(
        &mut self,
        scope: MirScopeIdx,
        place: &mut Option<MirPlace>,
        ty: SigTy,
    ) -> MirPlace {
        let tcx = self.tcx();

        *place.get_or_insert_with(|| MirPlace {
            local: self.push_local(scope, MirLocal { ty }),
            projections: tcx.intern_list(&[]),
        })
    }
}
