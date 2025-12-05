use crate::{
    base::{
        Diag, ErrorGuaranteed, HardDiag, LeafDiag, Level,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::{
        ast::{
            AstBinOpKind, AstBlock, AstExpr, AstExprKind, AstMatchArm, AstStmt, AstStmtKind,
            AstStmtLet, AstUnOpKind,
        },
        token::Lifetime,
    },
    semantic::{
        lower::{entry::IntraItemLowerCtxt, func::path::ExprPathResolution},
        syntax::{
            AdtKind, AdtStructFieldSyntax, Block, Expr, ExprKind, LetChain, LetChainPart,
            LetChainPartKind, LetStmt, MatchArm, Pat, PatKind, SpannedTyOrReList, Stmt,
        },
    },
};

#[derive(Debug, Copy, Clone)]
pub enum LetChainDenyReason {
    NowhereNear,
    BrokenOut(AstBinOpKind, Span),
}

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
        self.lower_expr_with_deny_cause(ast, LetChainDenyReason::NowhereNear)
    }

    pub fn lower_expr_with_deny_cause(
        &mut self,
        ast: &AstExpr,
        let_deny_cause: LetChainDenyReason,
    ) -> Obj<Expr> {
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
            AstExprKind::Binary(op, op_span, lhs, rhs) => {
                let let_deny_cause = if *op == AstBinOpKind::And {
                    let_deny_cause
                } else {
                    LetChainDenyReason::BrokenOut(*op, *op_span)
                };

                ExprKind::Binary(
                    *op,
                    *op_span,
                    self.lower_expr_with_deny_cause(lhs, let_deny_cause),
                    self.lower_expr_with_deny_cause(rhs, let_deny_cause),
                )
            }
            AstExprKind::Unary(op, expr) => ExprKind::Unary(*op, self.lower_expr(expr)),
            AstExprKind::Lit(lit) => ExprKind::Literal(*lit),
            AstExprKind::Cast(expr, as_ty) => {
                ExprKind::Cast(self.lower_expr(expr), self.lower_ty(as_ty))
            }
            AstExprKind::Let(..) => match let_deny_cause {
                LetChainDenyReason::NowhereNear => ExprKind::Error(
                    Diag::span_err(
                        ast.span,
                        "`let` only allowed in statements or if-`let` chains",
                    )
                    .emit(),
                ),
                LetChainDenyReason::BrokenOut(op, span) => ExprKind::Error(
                    // TODO: improve `op` formatting
                    Diag::span_err(span, format_args!("{op:?} not allowed in if-`let` chain"))
                        .emit(),
                ),
            },
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

    pub fn lower_let_chain(&mut self, expr: &AstExpr) -> Obj<LetChain> {
        let s = &self.tcx.session;

        let mut fold_iter = expr;
        let mut prev_and_span = None;

        let mut parts = Vec::new();

        loop {
            if let AstExprKind::Binary(AstBinOpKind::And, op_span, lhs, rhs) = &fold_iter.kind {
                parts.push(self.lower_let_chain_part(prev_and_span.replace(*op_span), lhs));
                fold_iter = rhs;
            } else {
                parts.push(self.lower_let_chain_part(prev_and_span, fold_iter));
                break;
            }
        }

        Obj::new(
            LetChain {
                span: expr.span,
                parts: Obj::new_slice(&parts, s),
            },
            s,
        )
    }

    pub fn lower_let_chain_part(
        &mut self,
        prev_and_span: Option<Span>,
        expr: &AstExpr,
    ) -> Obj<LetChainPart> {
        let s = &self.tcx.session;

        let kind = match &expr.kind {
            AstExprKind::Let(pat, scrutinee, _eq_span) => {
                let scrutinee = self.lower_expr(scrutinee);
                let pat = self.lower_pat(pat);

                LetChainPartKind::Let(pat, scrutinee)
            }
            _ => LetChainPartKind::Expr(self.lower_expr(expr)),
        };

        Obj::new(
            LetChainPart {
                span: expr.span,
                prev_and_span,
                kind,
            },
            s,
        )
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

            AstExprKind::Binary(AstBinOpKind::BitOr, _op_span, lhs, rhs) => {
                let mut accum = Vec::new();
                let mut fold_iter = rhs;

                accum.push(self.lower_lvalue_as_pat(lhs));

                loop {
                    if let AstExprKind::Binary(AstBinOpKind::BitOr, _op_span, lhs, rhs) =
                        &fold_iter.kind
                    {
                        accum.push(self.lower_lvalue_as_pat(lhs));
                        fold_iter = rhs;
                    } else {
                        accum.push(self.lower_lvalue_as_pat(fold_iter));
                        break;
                    }
                }

                PatKind::Or(Obj::new_slice(&accum, s))
            }

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
            | AstExprKind::Binary(AstBinOpKind::Add, ..)
            | AstExprKind::Binary(AstBinOpKind::Sub, ..)
            | AstExprKind::Binary(AstBinOpKind::Mul, ..)
            | AstExprKind::Binary(AstBinOpKind::Div, ..)
            | AstExprKind::Binary(AstBinOpKind::Rem, ..)
            | AstExprKind::Binary(AstBinOpKind::And, ..)
            | AstExprKind::Binary(AstBinOpKind::Or, ..)
            | AstExprKind::Binary(AstBinOpKind::BitXor, ..)
            | AstExprKind::Binary(AstBinOpKind::BitAnd, ..)
            | AstExprKind::Binary(AstBinOpKind::Shl, ..)
            | AstExprKind::Binary(AstBinOpKind::Shr, ..)
            | AstExprKind::Binary(AstBinOpKind::Eq, ..)
            | AstExprKind::Binary(AstBinOpKind::Lt, ..)
            | AstExprKind::Binary(AstBinOpKind::Le, ..)
            | AstExprKind::Binary(AstBinOpKind::Ne, ..)
            | AstExprKind::Binary(AstBinOpKind::Ge, ..)
            | AstExprKind::Binary(AstBinOpKind::Gt, ..)
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
