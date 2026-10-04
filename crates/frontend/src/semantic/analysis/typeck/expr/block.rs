use crate::{
    base::{
        Diag,
        arena::{HasInterner as _, HasListInterner as _, Obj},
    },
    semantic::{
        analysis::typeck::{BodyCtxt, infra::confirm::ThirExprConfirmedWithTy},
        infer::{HrtbUniverse, SpannedError},
        syntax::{
            Divergence, HirBlock, HirExpr, HirLabelledBlock, HirStmt, InferTyVarSourceInfo,
            LabelTargetKind, RelationMode, SimpleTyKind, ThirBlock, ThirBlockTrailing,
            ThirExprKind, ThirLetStmt, ThirStmt, Ty, TyKind,
        },
    },
};

impl BodyCtxt<'_, '_> {
    pub fn check_block_no_trailing(&mut self, block: Obj<HirBlock>) -> Divergence {
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

    pub fn create_thir_block_no_trailing(&mut self, block: Obj<HirBlock>) -> Obj<ThirBlock> {
        let s = self.session();

        Obj::new(
            ThirBlock {
                span: block.r(s).span,
                stmts: self.create_thir_block_stmts(block),
                last_expr: ThirBlockTrailing::MissingNotApplicable,
            },
            s,
        )
    }

    pub fn check_block_expr(
        &mut self,
        expr: Obj<HirExpr>,
        block: Obj<HirBlock>,
        demand_hint: Option<Ty>,
        divergence: &mut Divergence,
    ) -> ThirExprConfirmedWithTy {
        let tcx = self.tcx();
        let s = self.session();

        let label = HirLabelledBlock {
            target: expr,
            kind: LabelTargetKind::Block,
        };

        self.block_break_demands.insert(label, demand_hint);
        self.check_block_stmts(&block.r(s).stmts, divergence);

        let trailing_divergence = *divergence;

        let ty = if let Some(last_expr) = block.r(s).last_expr {
            if let Some(demand) = self.block_break_demands[&label] {
                self.check_expr_demand(last_expr, demand).and_do(divergence)
            } else {
                self.check_expr(last_expr, demand_hint).and_do(divergence)
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
            let s = bcx.session();
            let tcx = bcx.tcx();

            ThirExprKind::Block(Obj::new(
                ThirBlock {
                    span: block.r(s).span,
                    stmts: bcx.create_thir_block_stmts(block),
                    last_expr: match block.r(s).last_expr {
                        Some(last_expr) => {
                            ThirBlockTrailing::Present(bcx.confirm_thir_expr_post(last_expr))
                        }
                        None => match trailing_divergence {
                            Divergence::MustDiverge => ThirBlockTrailing::MissingCoerceNever,
                            Divergence::MayDiverge => ThirBlockTrailing::Present(
                                bcx.create_thir_unit_ctor(block.r(s).span),
                            ),
                        },
                    },
                },
                s,
            ))
        })
    }

    fn check_block_stmts(&mut self, stmts: &[HirStmt], divergence: &mut Divergence) {
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
                        let divergence = self.check_block_no_trailing(else_clause);

                        if divergence != Divergence::MustDiverge {
                            Diag::span_err(else_clause.r(s).span, "`else` block must diverge")
                                .emit();
                        }
                    }
                }
            }
        }
    }

    fn create_thir_block_stmts(&mut self, hir: Obj<HirBlock>) -> Vec<ThirStmt> {
        let s = self.session();

        hir.r(s)
            .stmts
            .iter()
            .map(|&stmt| match stmt {
                HirStmt::Expr(expr) => ThirStmt::Expr(self.confirm_thir_expr_post(expr)),
                HirStmt::Let(stmt) => ThirStmt::Let(Obj::new(
                    ThirLetStmt {
                        span: stmt.r(s).span,
                        pat: self.confirm_thir_pat(stmt.r(s).pat).outer,
                        init: self.confirm_opt_thir_expr_post(stmt.r(s).init),
                        else_clause: stmt
                            .r(s)
                            .else_clause
                            .map(|block| self.create_thir_block_no_trailing(block)),
                    },
                    s,
                )),
            })
            .collect::<Vec<_>>()
    }
}
