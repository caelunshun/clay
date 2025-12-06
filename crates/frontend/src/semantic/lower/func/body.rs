use crate::{
    base::{
        Diag, ErrorGuaranteed, HardDiag, LeafDiag, Level,
        arena::{LateInit, Obj},
    },
    parse::{
        ast::{
            AstBinOpKind, AstBinOpSpanned, AstBlock, AstExpr, AstExprKind, AstMatchArm, AstStmt,
            AstStmtKind, AstStmtLet, AstUnOpKind,
        },
        token::Lifetime,
    },
    semantic::{
        lower::{entry::IntraItemLowerCtxt, func::path::ExprPathResolution},
        syntax::{
            AdtKind, AdtStructFieldSyntax, Block, Expr, ExprKind, LetStmt, MatchArm, Pat, PatKind,
            SpannedTyOrReList, Stmt,
        },
    },
};

// === Body lowering === //

impl IntraItemLowerCtxt<'_> {
    pub fn lower_block_with_label(
        &mut self,
        owner: Obj<Expr>,
        label: Option<Lifetime>,
        block: &AstBlock,
    ) -> Obj<Block> {
        self.scoped(|this| {
            if let Some(label) = label {
                this.block_label_names
                    .define(label.name, (label.span, owner), |_| unreachable!());
            }

            this.lower_block_inner(block)
        })
    }

    pub fn lower_opt_block(&mut self, block: Option<&AstBlock>) -> Option<Obj<Block>> {
        block.map(|block| self.lower_block(block))
    }

    pub fn lower_block(&mut self, block: &AstBlock) -> Obj<Block> {
        self.scoped(|this| this.lower_block_inner(block))
    }

    fn lower_block_inner(&mut self, block: &AstBlock) -> Obj<Block> {
        let s = &self.tcx.session;

        let stmts = block
            .stmts
            .iter()
            .flat_map(|stmt| self.lower_stmt(stmt))
            .collect::<Vec<_>>();

        let last_expr = self.lower_opt_expr(block.last_expr.as_ref());

        Obj::new(
            Block {
                span: block.span,
                stmts,
                last_expr,
            },
            s,
        )
    }

    pub fn lower_block_as_expr(&mut self, block: &AstBlock) -> Obj<Expr> {
        let s = &self.tcx.session;
        let block = self.lower_block(block);

        Obj::new(
            Expr {
                span: block.r(s).span,
                kind: LateInit::new(ExprKind::Block(block)),
            },
            s,
        )
    }

    pub fn lower_stmt(&mut self, stmt: &AstStmt) -> Option<Stmt> {
        let s = &self.tcx.session;

        match &stmt.kind {
            AstStmtKind::Expr(expr) => Some(Stmt::Expr(self.lower_expr(expr))),
            AstStmtKind::Let(AstStmtLet {
                pat,
                ascription,
                init,
                else_clause,
            }) => {
                let init = self.lower_opt_expr(init.as_deref());
                let else_clause = self.lower_opt_block(else_clause.as_deref());
                let pat = self.lower_pat(pat);

                Some(Stmt::Let(Obj::new(
                    LetStmt {
                        span: stmt.span,
                        pat,
                        ascription: self.lower_opt_ty(ascription.as_deref()),
                        init,
                        else_clause,
                    },
                    s,
                )))
            }
            AstStmtKind::Item(..) => {
                // (already lowered elsewhere)
                None
            }
        }
    }

    pub fn lower_exprs(&mut self, exprs: &[AstExpr]) -> Obj<[Obj<Expr>]> {
        let s = &self.tcx.session;

        Obj::new_iter(exprs.iter().map(|expr| self.lower_expr(expr)), s)
    }

    pub fn lower_opt_expr(&mut self, expr: Option<&AstExpr>) -> Option<Obj<Expr>> {
        expr.map(|v| self.lower_expr(v))
    }

    pub fn lower_expr(&mut self, ast: &AstExpr) -> Obj<Expr> {
        let s = &self.tcx.session;

        let expr = Obj::new(
            Expr {
                span: ast.span,
                kind: LateInit::uninit(),
            },
            s,
        );

        let kind = match &ast.kind {
            AstExprKind::Array(exprs) => ExprKind::Array(self.lower_exprs(exprs)),
            AstExprKind::Call(callee, args) => {
                ExprKind::Call(self.lower_expr(callee), self.lower_exprs(args))
            }
            AstExprKind::Paren(expr) => {
                return self.lower_expr(expr);
            }
            AstExprKind::Tuple(exprs) => ExprKind::Tuple(self.lower_exprs(exprs)),
            AstExprKind::Binary(op, lhs, rhs) => {
                ExprKind::Binary(*op, self.lower_expr(lhs), self.lower_expr(rhs))
            }
            AstExprKind::Unary(op, expr) => ExprKind::Unary(*op, self.lower_expr(expr)),
            AstExprKind::Lit(lit) => ExprKind::Literal(*lit),
            AstExprKind::Cast(expr, as_ty) => {
                ExprKind::Cast(self.lower_expr(expr), self.lower_ty(as_ty))
            }
            AstExprKind::Let(..) => ExprKind::Error(
                Diag::span_err(
                    ast.span,
                    "`let` only allowed in statements or if-`let` chains",
                )
                .emit(),
            ),
            AstExprKind::If {
                cond,
                truthy,
                falsy,
            } => self.scoped(|this| ExprKind::If {
                cond: this.lower_let_chain(cond),
                truthy: this.lower_block_as_expr(truthy),
                falsy: this.lower_opt_expr(falsy.as_deref()),
            }),
            AstExprKind::While { cond, block, label } => self.scoped(|this| {
                ExprKind::While(
                    this.lower_let_chain(cond),
                    this.lower_block_with_label(expr, *label, block),
                )
            }),
            AstExprKind::ForLoop {
                pat,
                iter,
                body,
                label,
            } => {
                let iter = self.lower_expr(iter);
                let pat = self.lower_pat(pat);
                let body = self.lower_block_with_label(expr, *label, body);

                ExprKind::ForLoop { pat, iter, body }
            }
            AstExprKind::Loop(block, label) => {
                ExprKind::Loop(self.lower_block_with_label(expr, *label, block))
            }
            AstExprKind::Match(scrutinee, arms) => ExprKind::Match(
                self.lower_expr(scrutinee),
                Obj::new_iter(arms.iter().map(|arm| self.lower_match_arm(arm)), s),
            ),
            AstExprKind::Block(block, label) => {
                ExprKind::Block(self.lower_block_with_label(expr, *label, block))
            }
            AstExprKind::Assign(lhs, rhs) => {
                ExprKind::Assign(self.lower_lvalue_as_pat(lhs), self.lower_expr(rhs))
            }
            AstExprKind::AssignOp(op, lhs, rhs) => {
                ExprKind::AssignOp(*op, self.lower_lvalue_as_pat(lhs), self.lower_expr(rhs))
            }
            AstExprKind::Field(expr, name) => ExprKind::Field(self.lower_expr(expr), *name),
            AstExprKind::GenericMethodCall {
                target,
                method,
                generics,
                args,
            } => {
                let (positional, associated) = self.lower_generic_params_syntactic(&generics.list);

                if let Some(associated) = associated.first() {
                    Diag::span_err(
                        associated.span,
                        "method does not have associated type constraints",
                    )
                    .emit();
                }

                ExprKind::GenericMethodCall {
                    target: self.lower_expr(target),
                    method: *method,
                    generics: SpannedTyOrReList::alloc_list(generics.span, &positional, self.tcx),
                    args: self.lower_exprs(args),
                }
            }
            AstExprKind::Index(expr, index) => {
                ExprKind::Index(self.lower_expr(expr), self.lower_expr(index))
            }
            AstExprKind::Range(lower, upper, limits) => ExprKind::Range(
                self.lower_opt_expr(lower.as_deref()),
                self.lower_opt_expr(upper.as_deref()),
                *limits,
            ),
            AstExprKind::Underscore => ExprKind::Error(
                Diag::span_err(
                    ast.span,
                    "in expressions, `_` can only be used on the left-hand side of an assignment",
                )
                .emit(),
            ),
            AstExprKind::Path(path) => 'path: {
                let res = match self.resolve_expr_path(path).fail_on_unbound_local() {
                    Ok(v) => v,
                    Err(err) => {
                        break 'path ExprKind::Error(err);
                    }
                };

                let unexpected_value = || -> HardDiag {
                    Diag::span_err(
                        path.span,
                        format_args!("expected value, got {}", res.bare_what(s)),
                    )
                };

                let validate_syntax =
                    |syntax: &AdtStructFieldSyntax, whats: &str| -> Option<ErrorGuaranteed> {
                        match syntax {
                            AdtStructFieldSyntax::Unit => None,
                            AdtStructFieldSyntax::Tuple => None,
                            AdtStructFieldSyntax::Named(_) => Some(
                                Diag::span_err(
                                    path.span,
                                    format_args!("expected value, got {}", res.bare_what(s)),
                                )
                                .child(LeafDiag::new(
                                    Level::Note,
                                    format_args!(
                                        "only unit and tuple {whats} can be turned into functions"
                                    ),
                                ))
                                .emit(),
                            ),
                        }
                    };

                match res {
                    ExprPathResolution::ResolvedSelfTy => {
                        // TODO
                        ExprKind::Error(crate::base::ErrorGuaranteed::new_unchecked())
                    }
                    ExprPathResolution::ResolvedAdt(def, args) => match def.r(s).kind {
                        AdtKind::Enum(_) => ExprKind::Error(unexpected_value().emit()),
                        AdtKind::Struct(def) => {
                            if let Some(err) = validate_syntax(&def.r(s).syntax, "`struct`s") {
                                break 'path ExprKind::Error(err);
                            }

                            ExprKind::StructCtorLit(def, args)
                        }
                    },
                    ExprPathResolution::ResolvedEnumVariant(def, args) => {
                        let descriptor = def.r(s).descriptor(s);

                        if let Some(err) =
                            validate_syntax(&descriptor.kind.r(s).syntax, "`enum` variants")
                        {
                            break 'path ExprKind::Error(err);
                        }

                        ExprKind::EnumCtorLit(def, args)
                    }
                    ExprPathResolution::ResolvedFn(def, args) => ExprKind::FuncLit(def, args),
                    ExprPathResolution::TypeRelative {
                        self_ty,
                        as_trait,
                        assoc,
                    } => ExprKind::TypeRelative {
                        self_ty,
                        as_trait,
                        assoc_name: assoc.name,
                        assoc_args: assoc.args,
                    },
                    ExprPathResolution::SelfLocal => {
                        // TODO: Validate against signature

                        ExprKind::SelfLocal
                    }
                    ExprPathResolution::Local(local) => ExprKind::Local(local),
                    ExprPathResolution::ResolvedModule(_)
                    | ExprPathResolution::ResolvedGeneric(_)
                    | ExprPathResolution::ResolvedTrait(_, _) => {
                        ExprKind::Error(unexpected_value().emit())
                    }
                }
            }
            AstExprKind::AddrOf(muta, expr) => {
                ExprKind::AddrOf(muta.as_muta(), self.lower_expr(expr))
            }
            AstExprKind::Break(label, expr) => ExprKind::Break {
                label: self.lookup_label(*label),
                expr: self.lower_opt_expr(expr.as_deref()),
            },
            AstExprKind::Continue(label) => ExprKind::Continue {
                label: self.lookup_label(*label),
            },
            AstExprKind::Return(expr) => ExprKind::Return(self.lower_opt_expr(expr.as_deref())),
            AstExprKind::Struct(ast_expr_path, ast_expr_fields, ast_struct_rest) => todo!(),
            AstExprKind::Error(err) => ExprKind::Error(*err),
        };

        LateInit::init(&expr.r(s).kind, kind);

        expr
    }

    pub fn lower_let_chain(&mut self, expr: &AstExpr) -> Obj<Expr> {
        let s = &self.tcx.session;

        #[derive(Debug, Copy, Clone)]
        enum BrokenOutViolation {
            NotYetReported(AstBinOpSpanned),
            AlreadyReported(ErrorGuaranteed),
        }

        let mut broken_out_violation = None;

        let parts = self
            .flatten_right_associative_bin_op_chain(expr, |_| true)
            .into_iter()
            .map(|(prev_op, expr)| {
                if let Some(prev_op) = prev_op
                    && prev_op.kind != AstBinOpKind::And
                {
                    broken_out_violation = Some(BrokenOutViolation::NotYetReported(prev_op));
                }

                let expr = if let Some(broken_out_violation) = &mut broken_out_violation {
                    match &expr.kind {
                        AstExprKind::Let(_pat, _scrutinee, _eq_span) => {
                            let err = match *broken_out_violation {
                                BrokenOutViolation::NotYetReported(culprit_op) => Diag::span_err(
                                    culprit_op.span,
                                    format_args!(
                                        "{} not allowed in if-`let` chain",
                                        culprit_op.kind.punct().expectation_name(),
                                    ),
                                )
                                .secondary(
                                    expr.span,
                                    format_args!(
                                        "`let` expression used here after the {}",
                                        culprit_op.kind.punct().expectation_name(),
                                    ),
                                )
                                .emit(),

                                // Leech off the previous error.
                                BrokenOutViolation::AlreadyReported(err) => err,
                            };

                            *broken_out_violation = BrokenOutViolation::AlreadyReported(err);

                            Obj::new(
                                Expr {
                                    span: expr.span,
                                    kind: LateInit::new(ExprKind::Error(err)),
                                },
                                s,
                            )
                        }
                        _ => self.lower_expr(expr),
                    }
                } else {
                    match &expr.kind {
                        AstExprKind::Let(pat, scrutinee, _eq_span) => {
                            let scrutinee = self.lower_expr(scrutinee);
                            let pat = self.lower_pat(pat);

                            Obj::new(
                                Expr {
                                    span: expr.span,
                                    kind: LateInit::new(ExprKind::Let(pat, scrutinee)),
                                },
                                s,
                            )
                        }
                        _ => self.lower_expr(expr),
                    }
                };

                (prev_op, expr)
            })
            .collect::<Vec<_>>();

        self.recombine_right_associative_bin_op_chain(parts)
    }

    pub fn lower_match_arm(&mut self, arm: &AstMatchArm) -> Obj<MatchArm> {
        self.scoped(|this| {
            let s = &this.tcx.session;
            let pat = this.lower_pat(&arm.pat);
            let guard = arm.guard.as_ref().map(|guard| this.lower_let_chain(guard));
            let body = this.lower_expr(&arm.body);

            Obj::new(
                MatchArm {
                    span: arm.span,
                    pat,
                    guard,
                    body,
                },
                s,
            )
        })
    }

    pub fn lower_lvalue_list_as_pat<'a>(
        &mut self,
        exprs: impl IntoIterator<Item = &'a AstExpr, IntoIter: ExactSizeIterator>,
    ) -> Obj<[Obj<Pat>]> {
        let s = &self.tcx.session;

        Obj::new_iter(
            exprs.into_iter().map(|expr| self.lower_lvalue_as_pat(expr)),
            s,
        )
    }

    pub fn lower_lvalue_as_pat(&mut self, expr: &AstExpr) -> Obj<Pat> {
        let s = &self.tcx.session;

        let kind = match &expr.kind {
            AstExprKind::Paren(expr) => {
                return self.lower_lvalue_as_pat(expr);
            }

            AstExprKind::Array(elems) => PatKind::Slice(self.lower_lvalue_list_as_pat(elems)),
            AstExprKind::Tuple(elems) => PatKind::Tuple(self.lower_lvalue_list_as_pat(elems)),
            AstExprKind::Lit(_) => PatKind::Lit(self.lower_expr(expr)),
            AstExprKind::Underscore => PatKind::Hole,

            AstExprKind::Binary(
                AstBinOpSpanned {
                    span: _,
                    kind: AstBinOpKind::BitOr,
                },
                _lhs,
                _rhs,
            ) => PatKind::Or(Obj::new_iter(
                self.flatten_right_associative_bin_op_chain(expr, |op| op == AstBinOpKind::BitOr)
                    .into_iter()
                    .map(|(_span, pat)| self.lower_lvalue_as_pat(pat)),
                s,
            )),

            AstExprKind::Struct(..) | AstExprKind::AddrOf(..) | AstExprKind::Call(..) => todo!(),

            AstExprKind::Block(..)
            | AstExprKind::Field(..)
            | AstExprKind::Index(..)
            | AstExprKind::Path(..)
            | AstExprKind::Unary(AstUnOpKind::Deref, ..) => {
                PatKind::PlaceExpr(self.lower_expr(expr))
            }

            AstExprKind::Cast(..)
            | AstExprKind::Let(..)
            | AstExprKind::If { .. }
            | AstExprKind::While { .. }
            | AstExprKind::ForLoop { .. }
            | AstExprKind::Loop(..)
            | AstExprKind::Match(..)
            | AstExprKind::Assign(..)
            | AstExprKind::AssignOp(..)
            | AstExprKind::GenericMethodCall { .. }
            | AstExprKind::Break(..)
            | AstExprKind::Continue(..)
            | AstExprKind::Return(..)
            | AstExprKind::Unary(AstUnOpKind::Not, ..)
            | AstExprKind::Unary(AstUnOpKind::Neg, ..)
            | AstExprKind::Binary(
                AstBinOpSpanned {
                    kind:
                        AstBinOpKind::Add
                        | AstBinOpKind::Sub
                        | AstBinOpKind::Mul
                        | AstBinOpKind::Div
                        | AstBinOpKind::Rem
                        | AstBinOpKind::And
                        | AstBinOpKind::Or
                        | AstBinOpKind::BitXor
                        | AstBinOpKind::BitAnd
                        | AstBinOpKind::Shl
                        | AstBinOpKind::Shr
                        | AstBinOpKind::Eq
                        | AstBinOpKind::Lt
                        | AstBinOpKind::Le
                        | AstBinOpKind::Ne
                        | AstBinOpKind::Ge
                        | AstBinOpKind::Gt,
                    ..
                },
                ..,
            )
            | AstExprKind::Range(..) => PatKind::Error(
                Diag::span_err(expr.span, "invalid left-hand side of assignment").emit(),
            ),

            AstExprKind::Error(err) => PatKind::Error(*err),
        };

        Obj::new(
            Pat {
                span: expr.span,
                kind,
            },
            s,
        )
    }
}

// === Utils === //

impl IntraItemLowerCtxt<'_> {
    pub fn flatten_right_associative_bin_op_chain<'ast>(
        &mut self,
        expr: &'ast AstExpr,
        mut filter_op: impl FnMut(AstBinOpKind) -> bool,
    ) -> Vec<(Option<AstBinOpSpanned>, &'ast AstExpr)> {
        let mut accum = Vec::new();
        let mut finger = expr;

        loop {
            if let AstExprKind::Binary(op, lhs, rhs) = &finger.kind
                && filter_op(op.kind)
            {
                accum.push((Some(*op), &**rhs));
                finger = lhs;
            } else {
                accum.push((None, finger));
                break;
            }
        }

        accum.reverse();

        accum
    }

    pub fn recombine_right_associative_bin_op_chain(
        &mut self,
        parts: impl IntoIterator<Item = (Option<AstBinOpSpanned>, Obj<Expr>)>,
    ) -> Obj<Expr> {
        let s = &self.tcx.session;

        let mut parts = parts.into_iter();
        let (outer_op, mut outer) = parts.next().unwrap();
        debug_assert!(outer_op.is_none());

        for (op, part) in parts {
            outer = Obj::new(
                Expr {
                    span: outer.r(s).span,
                    kind: LateInit::new(ExprKind::Binary(op.unwrap(), outer, part)),
                },
                s,
            );
        }

        outer
    }
}
