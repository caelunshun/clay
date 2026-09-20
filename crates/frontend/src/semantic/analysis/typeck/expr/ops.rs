use crate::{
    base::{
        Diag,
        arena::{HasInterner, HasListInterner as _, Obj},
    },
    parse::{
        ast::{AstAssignOpKind, AstBinOpKind, AstBinOpSpanned, AstLit, AstUnOpKind},
        token::{IntegralKind, NumLitBase, TokenNumLitKind},
    },
    semantic::{
        analysis::typeck::{BodyCtxt, infra::confirm::ThirExprConfirmedWithTy},
        infer::{ClauseCx, ClauseFuel, HrtbUniverse, PrettyFmtOpts, SpannedError, ToDebugTree},
        syntax::{
            Divergence, FloatKind, HirExpr, HirPat, InferTyVarSourceInfo, IntKind, RelationMode,
            SimpleTyKind, SimpleTySet, ThirExprKind, TraitItem, TraitParam, TraitSpec, Ty, TyKind,
            TyOrRe,
        },
    },
};

// === BodyCtxt === //

impl BodyCtxt<'_, '_> {
    pub fn check_expr_inner_lit(
        &mut self,
        expr: Obj<HirExpr>,
        lit: AstLit,
    ) -> ThirExprConfirmedWithTy {
        let tcx = self.tcx();

        let ty = match lit {
            AstLit::Number(lit) => {
                let constraints = match lit.kind {
                    // Has suffix
                    TokenNumLitKind::Integral {
                        base: _,
                        value: _,
                        suffix: Some(suffix),
                    } => match suffix {
                        IntegralKind::Int(IntKind::S8) => SimpleTySet::I8,
                        IntegralKind::Uint(IntKind::S8) => SimpleTySet::U8,
                        IntegralKind::Int(IntKind::S16) => SimpleTySet::I16,
                        IntegralKind::Uint(IntKind::S16) => SimpleTySet::U16,
                        IntegralKind::Int(IntKind::S32) => SimpleTySet::I32,
                        IntegralKind::Uint(IntKind::S32) => SimpleTySet::U32,
                        IntegralKind::Int(IntKind::S64) => SimpleTySet::I64,
                        IntegralKind::Uint(IntKind::S64) => SimpleTySet::U64,
                        IntegralKind::Float(FloatKind::S32) => SimpleTySet::F32,
                        IntegralKind::Float(FloatKind::S64) => SimpleTySet::F64,
                    },
                    TokenNumLitKind::Floating {
                        int_part: _,
                        dec_part: _,
                        exp_part: _,
                        suffix: Some(suffix),
                    } => match suffix {
                        FloatKind::S32 => SimpleTySet::F32,
                        FloatKind::S64 => SimpleTySet::F64,
                    },

                    // No suffix.
                    TokenNumLitKind::Integral {
                        base: NumLitBase::Decimal,
                        value: _,
                        suffix: None,
                    } => SimpleTySet::NUM,
                    TokenNumLitKind::Integral {
                        base: NumLitBase::Binary | NumLitBase::Hexadecimal | NumLitBase::Octal,
                        value: _,
                        suffix: None,
                    } => SimpleTySet::INT,
                    TokenNumLitKind::Floating {
                        int_part: _,
                        dec_part: _,
                        exp_part: _,
                        suffix: None,
                    } => SimpleTySet::FLOAT,
                };

                let var = self.ccx.fresh_ty_infer_var_restricted(
                    HrtbUniverse::ROOT,
                    InferTyVarSourceInfo::Literal { span: lit.span },
                    constraints,
                );
                self.register_infer_with_fallback(var);
                tcx.intern(TyKind::InferVar(var))
            }
            AstLit::Char(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Char)),
            AstLit::String(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Str)),
            AstLit::Bool(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Bool)),
        };

        self.put_thir_expr(expr, ty, move |bcx| ThirExprKind::CreateLiteral(lit))
    }

    pub fn check_expr_inner_bin_op(
        &mut self,
        expr: Obj<HirExpr>,
        kind: AstBinOpSpanned,
        lhs_expr: Obj<HirExpr>,
        rhs_expr: Obj<HirExpr>,
        divergence: &mut Divergence,
    ) -> ThirExprConfirmedWithTy {
        let s = self.session();
        let tcx = self.tcx();

        let lhs = self.check_expr(lhs_expr, None).and_do(divergence);
        let rhs = self.check_expr(rhs_expr, None).and_do(divergence);

        let kind_info = self.decode_bin_op_kind(kind.kind);

        // Attempt a primitive operation.
        let overload = 'try_prim_before_overload: {
            // We don't do `with_silent` but that's okay because we never poll this context until
            // accepted.
            let mut prim_fork = self.ccx().clone();

            let lhs = peel_ref_for_prim_op(&mut prim_fork, lhs);
            let rhs = peel_ref_for_prim_op(&mut prim_fork, rhs);

            if let Err(err) = prim_fork.unify_ty_and_simple_set(lhs, kind_info.lhs) {
                if let Some(overload) = kind_info.overload {
                    break 'try_prim_before_overload overload;
                }

                // TODO
                return self.put_thir_err(
                    expr,
                    Diag::anon_err(
                        SpannedError(lhs_expr.r(s).span, err)
                            .to_debug_tree(&self.ccx().pretty(PrettyFmtOpts::default())),
                    )
                    .emit(),
                );
            }

            match kind_info.rhs {
                EquateOrSet::EqualsLhs => {
                    match prim_fork.unify_ty_and_ty(lhs, rhs, RelationMode::Equate) {
                        Ok(promise) => {
                            promise.report_loud();
                        }
                        Err(err) => {
                            if let Some(overload) = kind_info.overload {
                                break 'try_prim_before_overload overload;
                            }

                            // TODO
                            return self.put_thir_err(
                                expr,
                                Diag::anon_err(
                                    SpannedError(rhs_expr.r(s).span, *err).to_debug_tree(
                                        &self.ccx().pretty(PrettyFmtOpts::default()),
                                    ),
                                )
                                .emit(),
                            );
                        }
                    }
                }
                EquateOrSet::Unrelated(rhs_set) => {
                    if let Err(err) = prim_fork.unify_ty_and_simple_set(lhs, rhs_set) {
                        if let Some(overload) = kind_info.overload {
                            break 'try_prim_before_overload overload;
                        }

                        // TODO
                        return self.put_thir_err(
                            expr,
                            Diag::anon_err(
                                SpannedError(lhs_expr.r(s).span, err)
                                    .to_debug_tree(&self.ccx().pretty(PrettyFmtOpts::default())),
                            )
                            .emit(),
                        );
                    }
                }
            }

            *self.ccx_mut() = prim_fork;

            let ty = match kind_info.out {
                EquateOrTy::EqualsLhs => lhs,
                EquateOrTy::Unrelated(ty) => ty,
            };

            return self.put_thir_expr(expr, ty, |bcx| todo!());
        };

        // Otherwise, attempt to perform an overloaded operation.
        let result_ty = self.ccx_mut().fresh_ty_infer(
            HrtbUniverse::ROOT,
            InferTyVarSourceInfo::OverloadedResult { span: kind.span },
        );

        self.ccx_mut()
            .oblige_ty_meets_trait_instantiated(
                ClauseFuel::new(),
                HrtbUniverse::ROOT,
                lhs,
                TraitSpec {
                    def: overload,
                    params: tcx.intern_list(&[
                        TraitParam::Equals(TyOrRe::Ty(rhs)),
                        TraitParam::Equals(TyOrRe::Ty(result_ty)),
                    ]),
                },
            )
            // TODO
            .map({
                let span = expr.r(s).span;
                move |_ccx, error| SpannedError(span, error)
            })
            .report_loud();

        self.put_thir_expr(expr, result_ty, |bcx| todo!())
    }

    pub fn check_expr_inner_un_op(
        &mut self,
        expr: Obj<HirExpr>,
        kind: AstUnOpKind,
        lhs: Obj<HirExpr>,
        divergence: &mut Divergence,
    ) -> ThirExprConfirmedWithTy {
        let s = self.session();
        let tcx = self.tcx();

        let lhs_ty = self.check_expr(lhs, None).and_do(divergence);

        let kind_info = self.decode_un_op_kind(kind);

        // Attempt a primitive operation.
        {
            let lhs_ty = peel_ref_for_prim_op(self.ccx_mut(), lhs_ty);

            if self
                .ccx_mut()
                .unify_ty_and_simple_set(lhs_ty, kind_info.lhs)
                .is_ok()
            {
                return self.put_thir_expr(expr, lhs_ty, |bcx| todo!());
            }
        }

        if kind == AstUnOpKind::Deref
            && let lhs_ty = self.ccx_mut().peel_ty_infer_var_after_poll(lhs_ty)
            && let TyKind::Reference(_re, _muta, pointee) = *lhs_ty.r(s)
        {
            return self.put_thir_expr(expr, pointee, |bcx| todo!());
        }

        // Otherwise, attempt to perform an overloaded operation.
        let result_ty = self.ccx_mut().fresh_ty_infer(
            HrtbUniverse::ROOT,
            InferTyVarSourceInfo::OverloadedResult {
                span: expr.r(s).span,
            },
        );

        self.ccx_mut()
            .oblige_ty_meets_trait_instantiated(
                ClauseFuel::new(),
                HrtbUniverse::ROOT,
                lhs_ty,
                TraitSpec {
                    def: kind_info.overload.unwrap(),
                    params: tcx.intern_list(&[TraitParam::Equals(TyOrRe::Ty(result_ty))]),
                },
            )
            // TODO
            .map({
                let span = expr.r(s).span;

                move |_ccx, error| SpannedError(span, error)
            })
            .report_loud();

        self.put_thir_expr(expr, result_ty, |bcx| todo!())
    }

    pub fn check_expr_inner_assign_op(
        &mut self,
        expr: Obj<HirExpr>,
        kind: AstAssignOpKind,
        lhs: Obj<HirPat>,
        rhs: Obj<HirExpr>,
        divergence: &mut Divergence,
    ) -> ThirExprConfirmedWithTy {
        let tcx = self.tcx();
        let s = self.session();

        'assign: {
            let lhs = self.check_pat_infer(lhs, Some(divergence));
            let rhs = self.check_expr(rhs, None).and_do(divergence);

            let kind_info = self.decode_assign_op_kind(kind);

            // Attempt a primitive operation.
            'try_prim: {
                // See above.
                let mut prim_fork = self.ccx().clone();

                let lhs = peel_ref_for_prim_op(&mut prim_fork, lhs);
                let rhs = peel_ref_for_prim_op(&mut prim_fork, rhs);

                if prim_fork
                    .unify_ty_and_simple_set(lhs, kind_info.lhs)
                    .is_err()
                {
                    break 'try_prim;
                }

                match kind_info.rhs {
                    EquateOrSet::EqualsLhs => {
                        match prim_fork.unify_ty_and_ty(lhs, rhs, RelationMode::Equate) {
                            Ok(promise) => {
                                promise.report_loud();
                            }
                            Err(_) => {
                                break 'try_prim;
                            }
                        }
                    }
                    EquateOrSet::Unrelated(rhs_set) => {
                        if prim_fork.unify_ty_and_simple_set(lhs, rhs_set).is_err() {
                            break 'try_prim;
                        }
                    }
                }

                *self.ccx_mut() = prim_fork;

                let ty = tcx.intern(TyKind::Tuple(tcx.intern_list(&[])));

                return self.put_thir_expr(expr, ty, |bcx| todo!());
            }

            // Otherwise, attempt to perform an overloaded operation.
            let result_ty = self.ccx_mut().fresh_ty_infer(
                HrtbUniverse::ROOT,
                InferTyVarSourceInfo::OverloadedResult {
                    span: expr.r(s).span,
                },
            );

            self.ccx_mut()
                .oblige_ty_meets_trait_instantiated(
                    ClauseFuel::new(),
                    HrtbUniverse::ROOT,
                    lhs,
                    TraitSpec {
                        def: kind_info.overload.unwrap(),
                        params: tcx.intern_list(&[
                            TraitParam::Equals(TyOrRe::Ty(rhs)),
                            TraitParam::Equals(TyOrRe::Ty(result_ty)),
                        ]),
                    },
                )
                // TODO
                .map({
                    let span = expr.r(s).span;

                    move |_ccx, error| SpannedError(span, error)
                })
                .report_loud();
        }

        let ty = tcx.intern(TyKind::Tuple(tcx.intern_list(&[])));

        self.put_thir_expr(expr, ty, |bcx| todo!())
    }

    pub fn check_expr_inner_index(
        &mut self,
        expr: Obj<HirExpr>,
        target: Obj<HirExpr>,
        index: Obj<HirExpr>,
        divergence: &mut Divergence,
    ) -> ThirExprConfirmedWithTy {
        let tcx = self.tcx();
        let s = self.session();

        let target_ty = self.check_expr(target, None).and_do(divergence);
        let index_ty = self.ccx_mut().fresh_ty_infer(
            HrtbUniverse::ROOT,
            InferTyVarSourceInfo::IndexInput {
                span: index.r(s).span,
            },
        );
        let output_ty = self.ccx_mut().fresh_ty_infer(
            HrtbUniverse::ROOT,
            InferTyVarSourceInfo::IndexOutput {
                span: expr.r(s).span,
            },
        );

        let index_trait = self.krate().r(s).lang_items.index_trait().unwrap();

        self.ccx_mut()
            .oblige_ty_meets_trait_instantiated(
                ClauseFuel::new(),
                HrtbUniverse::ROOT,
                target_ty,
                TraitSpec {
                    def: index_trait,
                    params: tcx.intern_list(&[
                        TraitParam::Equals(TyOrRe::Ty(index_ty)),
                        TraitParam::Equals(TyOrRe::Ty(output_ty)),
                    ]),
                },
            )
            // TODO
            .map({
                let span = expr.r(s).span;
                move |_ccx, error| SpannedError(span, error)
            })
            .report_loud();

        self.check_expr_demand(index, index_ty).and_do(divergence);

        self.put_thir_expr(expr, output_ty, |bcx| todo!())
    }
}

// === Helpers === //

#[derive(Debug, Copy, Clone)]
pub struct UnaryOperation {
    pub lhs: SimpleTySet,
    pub overload: Option<Obj<TraitItem>>,
}

#[derive(Debug, Copy, Clone)]
pub struct BinaryOperation {
    pub lhs: SimpleTySet,
    pub rhs: EquateOrSet,
    pub out: EquateOrTy,
    pub overload: Option<Obj<TraitItem>>,
}

#[derive(Debug, Copy, Clone)]
pub struct AssignOperation {
    pub lhs: SimpleTySet,
    pub rhs: EquateOrSet,
    pub overload: Option<Obj<TraitItem>>,
}

#[derive(Debug, Copy, Clone)]
pub enum EquateOrSet {
    EqualsLhs,
    Unrelated(SimpleTySet),
}

#[derive(Debug, Copy, Clone)]
pub enum EquateOrTy {
    EqualsLhs,
    Unrelated(Ty),
}

pub fn peel_ref_for_prim_op(ccx: &mut ClauseCx<'_>, ty: Ty) -> Ty {
    let s = ccx.session();

    let ty = ccx.peel_ty_infer_var_after_poll(ty);

    match *ty.r(s) {
        TyKind::Reference(_re, _muta, pointee) => pointee,
        _ => ty,
    }
}

// Inspired by `enforce_builtin_binop_types` in `rustc`.
impl BodyCtxt<'_, '_> {
    pub fn decode_un_op_kind(&self, op: AstUnOpKind) -> UnaryOperation {
        let s = self.session();
        let lang_items = &self.krate().r(s).lang_items;

        match op {
            AstUnOpKind::Deref => UnaryOperation {
                lhs: SimpleTySet::empty(),
                overload: lang_items.deref_trait(),
            },
            AstUnOpKind::Not => UnaryOperation {
                lhs: SimpleTySet::INT | SimpleTySet::BOOL,
                overload: lang_items.not_trait(),
            },
            AstUnOpKind::Neg => UnaryOperation {
                lhs: SimpleTySet::SIGNED_NUM,
                overload: lang_items.neg_trait(),
            },
        }
    }

    pub fn decode_bin_op_kind(&self, op: AstBinOpKind) -> BinaryOperation {
        let s = self.session();
        let tcx = self.tcx();
        let lang_items = &self.krate().r(s).lang_items;

        match op {
            AstBinOpKind::Add => BinaryOperation {
                lhs: SimpleTySet::NUM,
                rhs: EquateOrSet::EqualsLhs,
                out: EquateOrTy::EqualsLhs,
                overload: lang_items.add_trait(),
            },
            AstBinOpKind::Sub => BinaryOperation {
                lhs: SimpleTySet::NUM,
                rhs: EquateOrSet::EqualsLhs,
                out: EquateOrTy::EqualsLhs,
                overload: lang_items.sub_trait(),
            },
            AstBinOpKind::Mul => BinaryOperation {
                lhs: SimpleTySet::NUM,
                rhs: EquateOrSet::EqualsLhs,
                out: EquateOrTy::EqualsLhs,
                overload: lang_items.mul_trait(),
            },
            AstBinOpKind::Div => BinaryOperation {
                lhs: SimpleTySet::NUM,
                rhs: EquateOrSet::EqualsLhs,
                out: EquateOrTy::EqualsLhs,
                overload: lang_items.div_trait(),
            },
            AstBinOpKind::Rem => BinaryOperation {
                lhs: SimpleTySet::NUM,
                rhs: EquateOrSet::EqualsLhs,
                out: EquateOrTy::EqualsLhs,
                overload: lang_items.rem_trait(),
            },
            AstBinOpKind::And | AstBinOpKind::Or => BinaryOperation {
                lhs: SimpleTySet::BOOL,
                rhs: EquateOrSet::EqualsLhs,
                out: EquateOrTy::EqualsLhs,
                overload: None,
            },
            AstBinOpKind::BitXor => BinaryOperation {
                lhs: SimpleTySet::INT | SimpleTySet::BOOL,
                rhs: EquateOrSet::EqualsLhs,
                out: EquateOrTy::EqualsLhs,
                overload: lang_items.bit_xor_trait(),
            },
            AstBinOpKind::BitAnd => BinaryOperation {
                lhs: SimpleTySet::INT | SimpleTySet::BOOL,
                rhs: EquateOrSet::EqualsLhs,
                out: EquateOrTy::EqualsLhs,
                overload: lang_items.bit_and_trait(),
            },
            AstBinOpKind::BitOr => BinaryOperation {
                lhs: SimpleTySet::INT | SimpleTySet::BOOL,
                rhs: EquateOrSet::EqualsLhs,
                out: EquateOrTy::EqualsLhs,
                overload: lang_items.bit_or_trait(),
            },
            AstBinOpKind::Shl => BinaryOperation {
                lhs: SimpleTySet::INT,
                rhs: EquateOrSet::Unrelated(SimpleTySet::INT),
                out: EquateOrTy::EqualsLhs,
                overload: lang_items.bit_shl_trait(),
            },
            AstBinOpKind::Shr => BinaryOperation {
                lhs: SimpleTySet::INT,
                rhs: EquateOrSet::Unrelated(SimpleTySet::INT),
                out: EquateOrTy::EqualsLhs,
                overload: lang_items.bit_shr_trait(),
            },
            AstBinOpKind::Eq => BinaryOperation {
                lhs: SimpleTySet::NUM | SimpleTySet::BOOL,
                rhs: EquateOrSet::EqualsLhs,
                out: EquateOrTy::Unrelated(tcx.intern(TyKind::Simple(SimpleTyKind::Bool))),
                overload: lang_items.partial_eq_trait(),
            },
            AstBinOpKind::Lt
            | AstBinOpKind::Le
            | AstBinOpKind::Ne
            | AstBinOpKind::Ge
            | AstBinOpKind::Gt => BinaryOperation {
                lhs: SimpleTySet::NUM,
                rhs: EquateOrSet::EqualsLhs,
                out: EquateOrTy::Unrelated(tcx.intern(TyKind::Simple(SimpleTyKind::Bool))),
                overload: lang_items.ord_trait(),
            },
        }
    }

    pub fn decode_assign_op_kind(&self, op: AstAssignOpKind) -> AssignOperation {
        let s = self.session();
        let lang_items = &self.krate().r(s).lang_items;

        match op {
            AstAssignOpKind::Add => AssignOperation {
                lhs: SimpleTySet::NUM,
                rhs: EquateOrSet::EqualsLhs,
                overload: lang_items.add_assign_trait(),
            },
            AstAssignOpKind::Sub => AssignOperation {
                lhs: SimpleTySet::NUM,
                rhs: EquateOrSet::EqualsLhs,
                overload: lang_items.sub_assign_trait(),
            },
            AstAssignOpKind::Mul => AssignOperation {
                lhs: SimpleTySet::NUM,
                rhs: EquateOrSet::EqualsLhs,
                overload: lang_items.mul_assign_trait(),
            },
            AstAssignOpKind::Div => AssignOperation {
                lhs: SimpleTySet::NUM,
                rhs: EquateOrSet::EqualsLhs,
                overload: lang_items.div_assign_trait(),
            },
            AstAssignOpKind::Rem => AssignOperation {
                lhs: SimpleTySet::NUM,
                rhs: EquateOrSet::EqualsLhs,
                overload: lang_items.rem_assign_trait(),
            },
            AstAssignOpKind::BitXor => AssignOperation {
                lhs: SimpleTySet::INT | SimpleTySet::BOOL,
                rhs: EquateOrSet::EqualsLhs,
                overload: lang_items.bit_xor_assign_trait(),
            },
            AstAssignOpKind::BitAnd => AssignOperation {
                lhs: SimpleTySet::INT | SimpleTySet::BOOL,
                rhs: EquateOrSet::EqualsLhs,
                overload: lang_items.bit_and_assign_trait(),
            },
            AstAssignOpKind::BitOr => AssignOperation {
                lhs: SimpleTySet::INT | SimpleTySet::BOOL,
                rhs: EquateOrSet::EqualsLhs,
                overload: lang_items.bit_or_assign_trait(),
            },
            AstAssignOpKind::Shl => AssignOperation {
                lhs: SimpleTySet::INT,
                rhs: EquateOrSet::Unrelated(SimpleTySet::INT),
                overload: lang_items.bit_shl_assign_trait(),
            },
            AstAssignOpKind::Shr => AssignOperation {
                lhs: SimpleTySet::INT,
                rhs: EquateOrSet::Unrelated(SimpleTySet::INT),
                overload: lang_items.bit_shr_assign_trait(),
            },
        }
    }
}
