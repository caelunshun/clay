use crate::{
    base::{
        Diag, ErrorGuaranteed, HardDiag, LeafDiag, Level,
        arena::{LateInit, Obj},
    },
    parse::{
        ast::{
            AstBinOpKind, AstBlock, AstExpr, AstExprKind, AstPat, AstPatKind, AstStmt, AstStmtKind,
            AstStmtLet, AstUnOpKind,
        },
        token::Lifetime,
    },
    semantic::{
        lower::{entry::IntraItemLowerCtxt, func::path::ExprPathResolution},
        syntax::{
            AdtKind, AdtStructFieldSyntax, Block, Expr, ExprKind, LetStmt, Pat, PatKind, Stmt,
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
            }) => Some(Stmt::Let(Obj::new(
                LetStmt {
                    span: stmt.span,
                    pat: self.lower_pat(pat, PatLoweringMode::Defining),
                    ascription: self.lower_opt_ty(ascription.as_deref()),
                    init: self.lower_opt_expr(init.as_deref()),
                    else_clause: self.lower_opt_block(else_clause.as_deref()),
                },
                s,
            ))),
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
            AstExprKind::Let(..) => {
                unreachable!()
            }
            AstExprKind::If {
                cond,
                truthy,
                falsy,
            } => ExprKind::If {
                cond: self.lower_expr(cond),
                truthy: self.lower_block_as_expr(truthy),
                falsy: self.lower_opt_expr(falsy.as_deref()),
            },
            AstExprKind::While { cond, block, label } => ExprKind::While(
                self.lower_expr(cond),
                self.lower_block_with_label(expr, *label, block),
            ),
            AstExprKind::ForLoop {
                pat,
                iter,
                body,
                label,
            } => ExprKind::ForLoop {
                pat: self.lower_pat(pat, PatLoweringMode::Defining),
                iter: self.lower_expr(iter),
                body: self.lower_block_with_label(expr, *label, body),
            },
            AstExprKind::Loop(block, label) => {
                ExprKind::Loop(self.lower_block_with_label(expr, *label, block))
            }
            AstExprKind::Match(ast_expr, ast_match_arms) => todo!(),
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
            AstExprKind::GenericMethod {
                target,
                method,
                generics,
                args,
            } => todo!(),
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
                let res = match self.resolve_expr_path(path) {
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

                            // TODO
                            ExprKind::Error(crate::base::ErrorGuaranteed::new_unchecked())
                        }
                    },
                    ExprPathResolution::ResolvedEnumVariant(def, args) => {
                        let descriptor = def.r(s).descriptor(s);

                        if let Some(err) =
                            validate_syntax(&descriptor.kind.r(s).syntax, "`enum` variants")
                        {
                            break 'path ExprKind::Error(err);
                        }

                        // TODO
                        ExprKind::Error(crate::base::ErrorGuaranteed::new_unchecked())
                    }
                    ExprPathResolution::ResolvedFn(obj, spanned) => {
                        // TODO
                        ExprKind::Error(crate::base::ErrorGuaranteed::new_unchecked())
                    }
                    ExprPathResolution::TypeRelative {
                        self_ty,
                        as_trait,
                        assoc,
                    } => {
                        // TODO
                        ExprKind::Error(crate::base::ErrorGuaranteed::new_unchecked())
                    }
                    ExprPathResolution::SelfLocal => {
                        // TODO
                        ExprKind::Error(crate::base::ErrorGuaranteed::new_unchecked())
                    }
                    ExprPathResolution::Local(obj) => {
                        // TODO
                        ExprKind::Error(crate::base::ErrorGuaranteed::new_unchecked())
                    }
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

    pub fn lower_pat_list(&mut self, asts: &[AstPat], mode: PatLoweringMode) -> Obj<[Obj<Pat>]> {
        let s = &self.tcx.session;

        Obj::new_iter(asts.iter().map(|ast| self.lower_pat(ast, mode)), s)
    }

    pub fn lower_pat(&mut self, ast: &AstPat, mode: PatLoweringMode) -> Obj<Pat> {
        let s = &self.tcx.session;

        let kind = match &ast.kind {
            AstPatKind::Wild => PatKind::Hole,
            AstPatKind::Path {
                binding_mode,
                path,
                and_bind,
            } => todo!(),
            AstPatKind::PathAndBrace(ast_expr_path, ast_pat_fields, ast_pat_struct_rest) => todo!(),
            AstPatKind::PathAndParen(ast_expr_path, ast_pats) => todo!(),
            AstPatKind::Or(pats) => PatKind::Or(self.lower_pat_list(pats, mode)),
            AstPatKind::Tuple(pats) => todo!(),
            AstPatKind::Ref(ast_opt_mutability, ast_pat) => todo!(),
            AstPatKind::Slice(ast_pats) => todo!(),
            AstPatKind::Rest => todo!(),
            AstPatKind::Paren(ast_pat) => todo!(),
            AstPatKind::Range(ast_expr, ast_expr1, ast_range_limits) => todo!(),
            AstPatKind::Lit(ast_expr) => todo!(),
            AstPatKind::Error(err) => PatKind::Error(*err),
        };

        Obj::new(
            Pat {
                span: ast.span,
                kind,
            },
            s,
        )
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

            AstExprKind::Array(elems) => PatKind::Array(self.lower_lvalue_list_as_pat(elems)),
            AstExprKind::Tuple(elems) => PatKind::Tuple(self.lower_lvalue_list_as_pat(elems)),
            AstExprKind::Lit(lit) => PatKind::Lit(*lit),
            AstExprKind::Underscore => PatKind::Hole,

            AstExprKind::Binary(AstBinOpKind::BitOr, lhs, rhs) => {
                let mut accum = Vec::new();

                fn fold_or_pat(
                    ctxt: &mut IntraItemLowerCtxt<'_>,
                    accum: &mut Vec<Obj<Pat>>,
                    expr: &AstExpr,
                ) {
                    if let AstExprKind::Binary(AstBinOpKind::BitOr, lhs, rhs) = &expr.kind {
                        fold_or_pat(ctxt, accum, lhs);
                        fold_or_pat(ctxt, accum, rhs);
                    } else {
                        accum.push(ctxt.lower_lvalue_as_pat(expr));
                    }
                }

                fold_or_pat(self, &mut accum, lhs);
                fold_or_pat(self, &mut accum, rhs);

                PatKind::Or(Obj::new_slice(&accum, s))
            }

            AstExprKind::Struct(..)
            | AstExprKind::AddrOf(..)
            | AstExprKind::Range(..)
            | AstExprKind::Unary(AstUnOpKind::Neg, ..)
            | AstExprKind::Call(..) => todo!(),

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
            | AstExprKind::GenericMethod { .. }
            | AstExprKind::Break(..)
            | AstExprKind::Continue(..)
            | AstExprKind::Return(..)
            | AstExprKind::Unary(AstUnOpKind::Not, ..)
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
            | AstExprKind::Binary(AstBinOpKind::Gt, ..) => PatKind::Error(
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

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum PatLoweringMode {
    Defining,
    Destructuring,
}
