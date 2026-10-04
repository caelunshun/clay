use crate::{
    base::arena::{HasListInterner as _, Obj},
    semantic::{
        analysis::borrowck::build::{
            driver::{LabelledScope, MirFromThirCtx, MirRvalueOrPlace},
            scope::MirBuilderScopeIdx,
        },
        syntax::{
            MirAssignRvalue, MirOperand, MirPlace, MirPlaceElem, MirStmt, MirStmtKind,
            MirStmtSourceInfo, SigTy, ThirBlock, ThirBlockTrailing, ThirExpr, ThirExprKind,
            ThirStmt,
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
            ThirExprKind::CreateArray(obj) => todo!(),
            ThirExprKind::CreateTuple(elems) => {
                let assign_into =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                for (idx, &elem) in elems.r(s).iter().enumerate() {
                    self.lower_expr_place(
                        scope,
                        elem,
                        Some(assign_into.extend(tcx, [MirPlaceElem::Field(idx as u32)])),
                    );
                }

                MirRvalueOrPlace::Place(assign_into)
            }
            ThirExprKind::PrimitiveBinOp(op, lhs, rhs) => {
                MirRvalueOrPlace::Rvalue(MirAssignRvalue::BinaryOp(
                    op,
                    Box::new((
                        self.lower_expr_operand(scope, lhs),
                        self.lower_expr_operand(scope, rhs),
                    )),
                ))
            }
            ThirExprKind::PrimitiveUnOp(op, lhs) => {
                MirRvalueOrPlace::Rvalue(MirAssignRvalue::UnaryOp(
                    op,
                    MirOperand::Move(self.lower_expr_place(scope, lhs, None)),
                ))
            }
            ThirExprKind::NoOp(expr) => self.lower_expr_preferred(scope, expr, assign_into),
            ThirExprKind::Break(label, value) => todo!(),
            ThirExprKind::Continue(label) => todo!(),
            ThirExprKind::Return(obj) => todo!(),
            ThirExprKind::Assign(lhs, rhs) => todo!(),
            ThirExprKind::Block(block) => {
                let assign_into =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                let scope = self.builder.push_scope(scope);

                self.labelled_scopes.insert(
                    expr,
                    LabelledScope {
                        scope,
                        out_place: Some(assign_into),
                    },
                );

                self.lower_block(scope, block, Some(assign_into));

                MirRvalueOrPlace::Place(assign_into)
            }
            ThirExprKind::Loop(obj) => todo!(),
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
            ThirExprKind::Field(target, idx) => MirRvalueOrPlace::Place(
                self.lower_expr_place(scope, target, None)
                    .extend(tcx, [MirPlaceElem::Field(idx)]),
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
                todo!()
            }
            ThirExprKind::DynUse(dyn_site_idx, obj) => todo!(),
            ThirExprKind::Match(obj, obj1) => todo!(),
            ThirExprKind::While(cond, block) => todo!(),
            ThirExprKind::Let(obj, obj1) => todo!(),
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
                    self.lower_let(scope, stmt);
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
