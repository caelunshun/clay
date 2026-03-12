use crate::{
    base::{
        Diag,
        arena::{HasInterner, HasListInterner, Obj},
    },
    semantic::{
        analysis::{
            BodyCtxt, ClauseCxPrinter, ClauseOrigin, FloatingInferVar, OverloadResolution, TyCtxt,
            TyFoldable, TyFolder, TyFolderInfallibleExt,
        },
        syntax::{
            FnInstanceInner, FnOwner, HirBlock, HirExpr, HirExprKind, HirPat, HirStmt,
            InferTyVarSourceInfo, RelationMode, SpannedTy, ThirBlock, ThirExpr, ThirExprKind,
            ThirPat, ThirStmt, TraitParam, TraitSpec, Ty, TyKind, TyOrRe,
        },
    },
};
use std::convert::Infallible;

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn confirm(&mut self, body: Obj<HirExpr>) {
        let tcx = self.tcx();

        // Assign fallbacks to integer literal inference holes.
        self.ccx_mut().poll_obligations();

        for idx in 0..self.int_infers.len() {
            let var = self.int_infers[idx];

            let Err(FloatingInferVar { perm_set, .. }) =
                self.ccx().lookup_ty_infer_var_without_poll(var)
            else {
                continue;
            };

            let var_ty = tcx.intern(TyKind::InferVar(var));

            let Some(fallback) = perm_set.to_infer_fallback(tcx) else {
                continue;
            };

            _ = self.ucx_mut().unify_ty_and_ty(
                &ClauseOrigin::never_printed(),
                var_ty,
                fallback,
                RelationMode::Equate,
            );

            self.ccx_mut().poll_obligations();
        }

        // Lower the function to its THIR representation.
        self.confirm_expr(body);
    }

    fn confirm_expr(&mut self, expr: Obj<HirExpr>) -> Obj<ThirExpr> {
        // TODO: Apply coercions
        self.confirm_expr_without_adjustments(expr)
    }

    fn confirm_expr_list(&mut self, exprs: Obj<[Obj<HirExpr>]>) -> Obj<[Obj<ThirExpr>]> {
        let s = self.session();

        Obj::new_iter(exprs.r(s).iter().map(|&expr| self.confirm_expr(expr)), s)
    }

    fn confirm_expr_without_adjustments(&mut self, expr: Obj<HirExpr>) -> Obj<ThirExpr> {
        let s = self.session();
        let tcx = self.tcx();

        let ty = self.confirm_ty(self.expr_types_pre_coerce[&expr]);

        let kind = match *expr.r(s).kind {
            HirExprKind::Array(obj) => todo!(),
            HirExprKind::Call(callee, args) => {
                ThirExprKind::Call(self.confirm_expr(callee), self.confirm_expr_list(args))
            }
            HirExprKind::Tuple(elems) => ThirExprKind::CreateTuple(self.confirm_expr_list(elems)),
            HirExprKind::Binary(op, lhs, rhs) => {
                let lhs = self.confirm_expr(lhs);
                let rhs = self.confirm_expr(rhs);

                match self.overload_resolutions[&expr] {
                    OverloadResolution::Primitive => {
                        ThirExprKind::PrimitiveBinOp(op.kind, lhs, rhs)
                    }
                    OverloadResolution::Call => {
                        let overload = self.decode_bin_op_kind(op.kind).overload.unwrap();

                        ThirExprKind::Call(
                            Obj::new(
                                ThirExpr {
                                    span: expr.r(s).span,
                                    ty: tcx.intern(TyKind::FnDef(tcx.intern(FnInstanceInner {
                                        owner: FnOwner::Trait {
                                            instance: TraitSpec {
                                                def: overload,
                                                params: tcx.intern_list(&[
                                                    TraitParam::Equals(TyOrRe::Ty(rhs.r(s).ty)),
                                                    TraitParam::Equals(TyOrRe::Ty(ty)),
                                                ]),
                                            },
                                            self_ty: lhs.r(s).ty,
                                            method_idx: 0,
                                        },
                                        early_args: None,
                                    }))),
                                    kind: ThirExprKind::CreatePathZst,
                                },
                                s,
                            ),
                            Obj::new_slice(&[lhs, rhs], s),
                        )
                    }
                    OverloadResolution::Error(error) => ThirExprKind::Error(error),
                }
            }
            HirExprKind::Unary(op, lhs) => {
                let lhs = self.confirm_expr(lhs);

                match self.overload_resolutions[&expr] {
                    OverloadResolution::Primitive => ThirExprKind::PrimitiveUnOp(op, lhs),
                    OverloadResolution::Call => {
                        let overload = self.decode_un_op_kind(op).overload.unwrap();

                        ThirExprKind::Call(
                            Obj::new(
                                ThirExpr {
                                    span: expr.r(s).span,
                                    ty: tcx.intern(TyKind::FnDef(tcx.intern(FnInstanceInner {
                                        owner: FnOwner::Trait {
                                            instance: TraitSpec {
                                                def: overload,
                                                params: tcx.intern_list(&[TraitParam::Equals(
                                                    TyOrRe::Ty(ty),
                                                )]),
                                            },
                                            self_ty: lhs.r(s).ty,
                                            method_idx: 0,
                                        },
                                        early_args: None,
                                    }))),
                                    kind: ThirExprKind::CreatePathZst,
                                },
                                s,
                            ),
                            Obj::new_slice(&[lhs], s),
                        )
                    }
                    OverloadResolution::Error(error) => ThirExprKind::Error(error),
                }
            }
            HirExprKind::Literal(lit) => ThirExprKind::CreateLiteral(lit),
            HirExprKind::TupleOrUnitCtor(_) => ThirExprKind::CreatePathZst,
            HirExprKind::FnItemLit(_, _) => ThirExprKind::CreatePathZst,
            HirExprKind::TypeRelative {
                self_ty: _,
                as_trait: _,
                assoc_name: _,
                assoc_args: _,
            } => ThirExprKind::CreatePathZst,
            HirExprKind::Cast(target, _) => return self.confirm_expr(target),
            HirExprKind::If {
                cond,
                truthy,
                falsy,
            } => todo!(),
            HirExprKind::While(obj, obj1) => todo!(),
            HirExprKind::Let(obj, obj1) => todo!(),
            HirExprKind::ForLoop { pat, iter, body } => todo!(),
            HirExprKind::Loop(block) => ThirExprKind::Loop(
                self.confirm_block(block, tcx.intern(TyKind::Tuple(tcx.intern_list(&[])))),
            ),
            HirExprKind::Match(obj, obj1) => todo!(),
            HirExprKind::Block(block) => ThirExprKind::Block(self.confirm_block(block, ty)),
            HirExprKind::Assign(obj, obj1) => todo!(),
            HirExprKind::AssignOp(ast_assign_op_kind, obj, obj1) => todo!(),
            HirExprKind::Field(obj, ident) => todo!(),
            HirExprKind::MethodCall {
                receiver,
                name,
                generics,
                args,
            } => todo!(),
            HirExprKind::Index(obj, obj1) => todo!(),
            HirExprKind::Range(hir_range_expr) => todo!(),
            HirExprKind::LocalSelf => todo!(),
            HirExprKind::Local(local) => ThirExprKind::Local(local),
            HirExprKind::AddrOf(muta, expr) => ThirExprKind::AddrOf(muta, self.confirm_expr(expr)),
            HirExprKind::Break { label, value } => todo!(),
            HirExprKind::Continue(hir_labelled_block) => todo!(),
            HirExprKind::Return(expr) => ThirExprKind::Return(self.confirm_expr(expr)),
            HirExprKind::Struct(hir_struct_expr) => todo!(),
            HirExprKind::Error(error) => ThirExprKind::Error(error),
        };

        Obj::new(
            ThirExpr {
                span: expr.r(s).span,
                ty,
                kind,
            },
            s,
        )
    }

    fn confirm_block(&mut self, block: Obj<HirBlock>, ty: Ty) -> Obj<ThirBlock> {
        let s = self.session();

        let stmts = block
            .r(s)
            .stmts
            .iter()
            .map(|&stmt| self.confirm_stmt(stmt))
            .collect::<Vec<_>>();

        let last_expr = block.r(s).last_expr.map(|expr| self.confirm_expr(expr));

        Obj::new(
            ThirBlock {
                span: block.r(s).span,
                ty,
                stmts,
                last_expr,
            },
            s,
        )
    }

    fn confirm_stmt(&mut self, stmt: HirStmt) -> ThirStmt {
        match stmt {
            HirStmt::Expr(expr) => ThirStmt::Expr(self.confirm_expr(expr)),
            HirStmt::Let(obj) => todo!(),
        }
    }

    fn confirm_pat(&mut self, pat: Obj<HirPat>) -> Obj<ThirPat> {
        todo!()
    }

    fn confirm_ty<T: TyFoldable>(&mut self, ty: T) -> T {
        struct ConfirmFolder<'a, 'b, 'tcx> {
            bcx: &'a mut BodyCtxt<'b, 'tcx>,
        }

        impl<'tcx> TyFolder<'tcx> for ConfirmFolder<'_, '_, 'tcx> {
            type Error = Infallible;

            fn tcx(&self) -> &'tcx TyCtxt {
                self.bcx.tcx()
            }

            fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
                let s = self.session();
                let tcx = self.tcx();

                let TyKind::InferVar(var) = *ty.value.r(s) else {
                    return Ok(self.super_(ty.value));
                };

                if let Ok(resolved) = self.bcx.ccx().lookup_ty_infer_var_without_poll(var) {
                    return Ok(self.super_(resolved));
                }

                let var_ty = tcx.intern(TyKind::InferVar(var));

                let error = match self.bcx.ccx().lookup_infer_ty_src_info(var) {
                    InferTyVarSourceInfo::Local { name } => Diag::span_err(
                        name.span,
                        format_args!("type annotations required for local `{}`", name.text),
                    )
                    .emit(),
                    InferTyVarSourceInfo::HrtbLhsInstantiation { span }
                    | InferTyVarSourceInfo::ProjectionResult { span, .. }
                    | InferTyVarSourceInfo::Imported { span, .. }
                    | InferTyVarSourceInfo::FunctionArgs { span }
                    | InferTyVarSourceInfo::FunctionRetVal { span }
                    | InferTyVarSourceInfo::MethodReceiver { span }
                    | InferTyVarSourceInfo::OverloadedResult { span }
                    | InferTyVarSourceInfo::Literal { span }
                    | InferTyVarSourceInfo::ForLoopElem { span }
                    | InferTyVarSourceInfo::IndexInput { span }
                    | InferTyVarSourceInfo::IndexOutput { span }
                    | InferTyVarSourceInfo::LoopDemand { span }
                    | InferTyVarSourceInfo::HoleInfer { span }
                    | InferTyVarSourceInfo::PatType { span } => Diag::span_err(
                        span,
                        format_args!("failed to infer a type of `{}`", {
                            let mut printer = ClauseCxPrinter::new(self.bcx.ccx());
                            printer.push_ty(var_ty);
                            printer.finish()
                        }),
                    )
                    .emit(),

                    InferTyVarSourceInfo::UniversalElabHelper => todo!(),
                    InferTyVarSourceInfo::TraitAssocPlaceholderHelper => todo!(),
                    InferTyVarSourceInfo::UnifyHelper => todo!(),
                    InferTyVarSourceInfo::DerefHelper => todo!(),
                    InferTyVarSourceInfo::MethodLookupHelper => todo!(),
                };

                let error_ty = tcx.intern(TyKind::Error(error));

                _ = self.bcx.ucx_mut().unify_ty_and_ty(
                    &ClauseOrigin::never_printed(),
                    var_ty,
                    error_ty,
                    RelationMode::Equate,
                );

                self.bcx.ccx_mut().poll_obligations();

                Ok(error_ty)
            }
        }

        ConfirmFolder { bcx: self }.fold(ty)
    }
}
