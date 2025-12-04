use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag,
        analysis::SpannedViewEncode as _,
        arena::{LateInit, Obj},
        syntax::{HasSpan as _, Span},
    },
    parse::{
        ast::{
            AstBinOpKind, AstBlock, AstExpr, AstExprKind, AstExprPath, AstExprPathKind,
            AstParamedPath, AstParamedPathSegment, AstPat, AstPatKind, AstPathPartKw, AstStmt,
            AstStmtKind, AstStmtLet, AstTyKind, AstUnOpKind,
        },
        token::{Ident, Lifetime},
    },
    semantic::{
        lower::{
            entry::IntraItemLowerCtxt,
            modules::{FrozenModuleResolver, ParentResolver, PathResolver, StepResolveError},
        },
        syntax::{
            AdtDef, Block, EnumVariantItem, Expr, ExprKind, FuncLocal, ItemKind, LetStmt, Pat,
            PatKind, SpannedAdtInstanceView, SpannedTraitInstance, SpannedTy, SpannedTyOrReList,
            SpannedTyView, Stmt,
        },
    },
};
use std::slice;

// === Path resolution === //

#[derive(Debug, Clone)]
pub enum ExprPathResolution {
    /// A reference to the `Self` type by itself.
    ResolvedSelfTy,

    /// A reference to some resolved ADT with some optional generic parameters.
    ResolvedAdt(Obj<AdtDef>, SpannedTyOrReList),

    /// A reference to some resolved enum variant with some optional generic parameters.
    ResolvedEnumVariant(Obj<EnumVariantItem>, SpannedTyOrReList),

    /// A reference to a type with some further qualifications for methods or constants that cannot
    /// be solved at lowering time. Note that types without further qualifications will be treated
    /// as `Resolved` or `ResolvedSelfTy` to maintain exactly one representation for such scenarios.
    ///
    /// For example...
    ///
    /// - `Self::new`:
    ///     - `self_ty = This`
    ///     - `as_trait = None`
    ///     - `assoc_name = new`
    ///     - `assoc_args = None`
    /// - `Self::new::<u32>`:
    ///     - `self_ty = This`
    ///     - `as_trait = None`
    ///     - `assoc_name = new`
    ///     - `assoc_args = Some([u32])`
    /// - `<()>::woo`:
    ///     - `self_ty = ()`
    ///     - `as_trait = None`
    ///     - `assoc_name = woo`
    ///     - `assoc_args = None`
    /// - `T::new`:
    ///     - `self_ty = Universal(T)`
    ///     - `as_trait = None`
    ///     - `assoc_name = new`
    ///     - `assoc_args = None`
    /// - `MyTrait::foo`:
    ///     - `self_ty = ExplicitInfer`
    ///     - `as_trait = Some(MyTrait<_>)`
    ///     - `assoc_name = foo`
    ///     - `assoc_args = None`
    /// - `MyTrait::<u32>::foo`:
    ///     - `self_ty = ExplicitInfer`
    ///     - `as_trait = Some(MyTrait<u32>)`
    ///     - `assoc_name = foo`
    ///     - `assoc_args = None`
    ///
    TypeRelative {
        self_ty: SpannedTy,
        as_trait: Option<SpannedTraitInstance>,
        assoc: TypeRelativeAssoc,
    },

    /// The regular `self` keyword, which refers to a local.
    SelfLocal,

    /// A reference to a local defined within the current function.
    Local(Obj<FuncLocal>),
}

#[derive(Debug, Copy, Clone)]
pub struct TypeRelativeAssoc {
    pub name: Ident,
    pub args: Option<SpannedTyOrReList>,
}

impl IntraItemLowerCtxt<'_> {
    pub fn resolve_expr_path(
        &mut self,
        path: &AstExprPath,
    ) -> Result<ExprPathResolution, ErrorGuaranteed> {
        match &path.kind {
            AstExprPathKind::Bare(path) => self.resolve_bare_expr_path(path),
            AstExprPathKind::SelfTy(_self_kw, None) => Ok(ExprPathResolution::ResolvedSelfTy),
            AstExprPathKind::SelfTy(self_kw, Some(rest)) => Ok(ExprPathResolution::TypeRelative {
                self_ty: SpannedTyView::This.encode(*self_kw, self.tcx),
                as_trait: None,
                assoc: self.lower_rest_as_type_relative_assoc(rest)?,
            }),
            AstExprPathKind::Qualified(qual, rest) => Ok(ExprPathResolution::TypeRelative {
                self_ty: self.lower_ty(&qual.self_ty),
                as_trait: qual.as_trait.as_ref().and_then(|for_trait| {
                    let AstTyKind::Name(path, params) = &for_trait.kind else {
                        Diag::span_err(for_trait.span, "expected a trait, found a type").emit();

                        return None;
                    };

                    let Ok(def) = self.resolve_ty_item_path_as_trait(path) else {
                        return None;
                    };

                    self.lower_generics_of_trait_instance(def, for_trait.span, params.as_ref());

                    todo!()
                }),
                assoc: self.lower_rest_as_type_relative_assoc(rest)?,
            }),
            AstExprPathKind::Error(err) => Err(*err),
        }
    }

    fn resolve_bare_expr_path(
        &mut self,
        path: &AstParamedPath,
    ) -> Result<ExprPathResolution, ErrorGuaranteed> {
        let s = &self.tcx.session;

        // See whether we can resolve this as a `self` or as a function local.
        if let Some(first) = &path.segments.first()
            && let Some(ident) = first.part.ident()
            && let Some(local) = self.func_local_names.lookup(ident.text)
        {
            if let Some(args) = &first.args {
                Diag::span_err(
                    args.span,
                    "local variables cannot be instantiated with generic parameters",
                )
                .emit();
            }

            if let Some(subsequent) = &path.segments.get(1) {
                Diag::span_err(
                    subsequent.part.span(),
                    "local variables cannot be accessed like modules",
                )
                .emit();
            }

            return Ok(ExprPathResolution::Local(*local));
        }

        if let [first] = &path.segments[..]
            && first.part.keyword() == Some(AstPathPartKw::Self_)
        {
            if let Some(args) = &first.args {
                Diag::span_err(
                    args.span,
                    "`self` cannot be instantiated with generic parameters",
                )
                .emit();
            }

            return Ok(ExprPathResolution::SelfLocal);
        }

        // Otherwise, let's resolve a path.
        let mut finger = self.scope;
        let mut resolver = FrozenModuleResolver(s);
        let mut segments = path.segments.iter();

        while let Some(segment) = segments.next() {
            match resolver.resolve_step(self.root, self.scope, finger, segment.part) {
                Ok(target) => finger = target,
                Err(err) => {
                    return Err(err.emit(&resolver, finger, segment.part));
                }
            }

            match *finger.r(s).kind {
                ItemKind::Module(_) | ItemKind::Impl(_) => {
                    // (fallthrough)
                }
                ItemKind::EnumVariant(variant) => {
                    return Ok(self.resolve_bare_expr_path_from_enum_variant(
                        variant, None, segment, segments,
                    ));
                }
                ItemKind::Adt(adt) => {
                    return self.resolve_bare_expr_path_from_adt(adt, segment, segments);
                }
                ItemKind::Trait(def) => {
                    todo!()
                }
                ItemKind::Func(def) => {
                    todo!()
                }
            }

            if let Some(args) = &segment.args {
                Diag::span_err(
                    args.span,
                    format_args!(
                        "{} at `{}` does not accept generic parameters",
                        resolver.categorize(finger).a_what(),
                        resolver.path(finger),
                    ),
                )
                .emit();

                // (fallthrough)
            }
        }

        Err(Diag::span_err(
            path.span,
            format_args!(
                "path expressions cannot refer to {} `{}`",
                resolver.categorize(finger).bare_what(),
                resolver.path(finger),
            ),
        )
        .emit())
    }

    fn resolve_bare_expr_path_from_adt(
        &mut self,
        adt: Obj<AdtDef>,
        segment: &AstParamedPathSegment,
        mut segments: slice::Iter<'_, AstParamedPathSegment>,
    ) -> Result<ExprPathResolution, ErrorGuaranteed> {
        let s = &self.tcx.session;
        let mut resolver = FrozenModuleResolver(s);

        let first_generics = segment
            .args
            .as_ref()
            .map(|args| self.lower_generics_of_adt(adt, args.span, &args.list));

        if let Some(second_segment) = segments.next() {
            match resolver.resolve_step(self.root, self.scope, adt.r(s).item, second_segment.part) {
                Ok(variant) => {
                    let variant = variant.r(s).kind.as_enum_variant().unwrap();

                    Ok(self.resolve_bare_expr_path_from_enum_variant(
                        variant,
                        first_generics,
                        second_segment,
                        segments,
                    ))
                }
                Err(err @ StepResolveError::NotFound) => {
                    let Some(ident) = second_segment.part.ident() else {
                        return Err(err.emit(&resolver, adt.r(s).item, second_segment.part));
                    };

                    let self_ty = SpannedTyView::Adt(
                        SpannedAdtInstanceView {
                            def: adt,
                            params: first_generics.unwrap_or_else(|| {
                                self.synthesize_inferred_generics_for_elision(
                                    adt.r(s).generics,
                                    None,
                                    second_segment.part.span(),
                                )
                            }),
                        }
                        .encode(segment.part.span(), self.tcx),
                    )
                    .encode(segment.part.span(), self.tcx);

                    let assoc = TypeRelativeAssoc {
                        name: ident,
                        args: self.lower_type_relative_generics(second_segment.args.as_deref()),
                    };

                    Ok(ExprPathResolution::TypeRelative {
                        self_ty,
                        as_trait: None,
                        assoc,
                    })
                }
                Err(err) => Err(err.emit(&resolver, adt.r(s).item, second_segment.part)),
            }
        } else {
            let generics = first_generics.unwrap_or_else(|| {
                self.synthesize_inferred_generics_for_elision(
                    adt.r(s).generics,
                    None,
                    segment.part.span(),
                )
            });

            Ok(ExprPathResolution::ResolvedAdt(adt, generics))
        }
    }

    fn resolve_bare_expr_path_from_enum_variant(
        &mut self,
        variant: Obj<EnumVariantItem>,
        first_generics: Option<SpannedTyOrReList>,
        segment: &AstParamedPathSegment,
        mut segments: slice::Iter<'_, AstParamedPathSegment>,
    ) -> ExprPathResolution {
        let s = &self.tcx.session;
        let resolver = FrozenModuleResolver(s);

        if let Some(further) = segments.next() {
            StepResolveError::NotFound.emit(&resolver, variant.r(s).item, further.part);
        }

        let adt = variant.r(s).owner.r(s).kind.as_adt().unwrap();

        let second_generics = segment
            .args
            .as_ref()
            .map(|args| self.lower_generics_of_adt(adt, args.span, &args.list));

        if let (Some(first_generics), Some(second_generics)) = (first_generics, second_generics) {
            Diag::span_err(
                second_generics.own_span().unwrap_or(Span::DUMMY),
                "generic parameters for `enum` specified more than once",
            )
            .child(LeafDiag::span_note(
                first_generics.own_span().unwrap_or(Span::DUMMY),
                "generics first specified here",
            ))
            .emit();
        }

        let generics = first_generics.or(second_generics).unwrap_or_else(|| {
            self.synthesize_inferred_generics_for_elision(
                adt.r(s).generics,
                None,
                segment.part.span(),
            )
        });

        ExprPathResolution::ResolvedEnumVariant(variant, generics)
    }

    fn lower_rest_as_type_relative_assoc(
        &mut self,
        path: &AstParamedPath,
    ) -> Result<TypeRelativeAssoc, ErrorGuaranteed> {
        todo!()
    }
}

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
            AstExprKind::Path(path) => match self.resolve_expr_path(path) {
                Ok(_) => todo!(),
                Err(err) => ExprKind::Error(err),
            },
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
