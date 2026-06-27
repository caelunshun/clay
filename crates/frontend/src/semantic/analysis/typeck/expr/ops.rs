use crate::{
    base::arena::{HasInterner, HasListInterner as _, Obj},
    parse::ast::{AstAssignOpKind, AstBinOpKind, AstBinOpSpanned, AstUnOpKind},
    semantic::{
        analysis::typeck::{BodyCtxt, OverloadResolution},
        infer::{ClauseCx, ClauseError, HrtbUniverse, ObligeCause, ObligeCauseOrigin},
        syntax::{
            Divergence, HirExpr, HirPat, InferTyVarSourceInfo, RelationMode, SimpleTyKind,
            SimpleTySet, TraitItem, TraitParam, TraitSpec, Ty, TyKind, TyOrRe,
        },
    },
};

// === BodyCtxt === //

impl BodyCtxt<'_, '_> {
    pub fn check_expr_inner_bin_op(
        &mut self,
        expr: Obj<HirExpr>,
        kind: AstBinOpSpanned,
        lhs: Obj<HirExpr>,
        rhs: Obj<HirExpr>,
        divergence: &mut Divergence,
    ) -> Ty {
        let tcx = self.tcx();

        let lhs = self.check_expr(lhs, None).and_do(divergence);
        let rhs = self.check_expr(rhs, None).and_do(divergence);

        let kind_info = self.decode_bin_op_kind(kind.kind);
        let cause = ObligeCause::new_report(ObligeCauseOrigin::HirBodyCheckArithmetic {
            op_span: kind.span,
        });

        // Attempt a primitive operation.
        let mut prim_fork = self.ccx().clone();

        let fallback_err = 'try_prim: {
            let lhs = peel_ref_for_prim_op(&mut prim_fork, lhs);
            let rhs = peel_ref_for_prim_op(&mut prim_fork, rhs);

            if let Err(err) = prim_fork.unify_ty_and_simple_set(&cause, lhs, kind_info.lhs) {
                break 'try_prim ClauseError::TyAndSimpleTySetUnifyError(err);
            }

            match kind_info.rhs {
                EquateOrSet::EqualsLhs => {
                    if let Err(err) =
                        prim_fork.unify_ty_and_ty(&cause, lhs, rhs, RelationMode::Equate)
                    {
                        break 'try_prim ClauseError::TyAndTyUnifyError(*err);
                    }
                }
                EquateOrSet::Unrelated(rhs_set) => {
                    if let Err(err) = prim_fork.unify_ty_and_simple_set(&cause, lhs, rhs_set) {
                        break 'try_prim ClauseError::TyAndSimpleTySetUnifyError(err);
                    }
                }
            }

            *self.ccx_mut() = prim_fork;
            self.overload_resolutions
                .insert(expr, OverloadResolution::Primitive);

            return lhs;
        };

        // Otherwise, attempt to perform an overloaded operation.
        if let Some(overload) = kind_info.overload {
            let result_ty = self.ccx_mut().fresh_ty_infer(
                HrtbUniverse::ROOT,
                InferTyVarSourceInfo::OverloadedResult { span: kind.span },
            );

            self.ccx_mut().oblige_ty_meets_trait_instantiated(
                cause,
                HrtbUniverse::ROOT,
                lhs,
                TraitSpec {
                    def: overload,
                    params: tcx.intern_list(&[
                        TraitParam::Equals(TyOrRe::Ty(rhs)),
                        TraitParam::Equals(TyOrRe::Ty(result_ty)),
                    ]),
                },
            );

            self.overload_resolutions
                .insert(expr, OverloadResolution::Call);

            return result_ty;
        }

        let error = fallback_err.report(&prim_fork).unwrap();

        self.overload_resolutions
            .insert(expr, OverloadResolution::Error(error));

        tcx.intern(TyKind::Error(error))
    }

    pub fn check_expr_inner_un_op(
        &mut self,
        expr: Obj<HirExpr>,
        kind: AstUnOpKind,
        lhs: Obj<HirExpr>,
        divergence: &mut Divergence,
    ) -> Ty {
        let s = self.session();
        let tcx = self.tcx();

        let lhs_ty = self.check_expr(lhs, None).and_do(divergence);

        let kind_info = self.decode_un_op_kind(kind);
        let cause = ObligeCause::new_report(ObligeCauseOrigin::HirBodyCheckArithmetic {
            op_span: lhs.r(s).span,
        });

        // Attempt a primitive operation.
        let fallback_err = {
            let lhs_ty = peel_ref_for_prim_op(self.ccx_mut(), lhs_ty);

            match self
                .ccx_mut()
                .unify_ty_and_simple_set(&cause, lhs_ty, kind_info.lhs)
            {
                Ok(()) => {
                    self.overload_resolutions
                        .insert(expr, OverloadResolution::Primitive);

                    return lhs_ty;
                }
                Err(err) => err,
            }
        };

        if kind == AstUnOpKind::Deref
            && let lhs_ty = self.ccx_mut().peel_ty_infer_var_after_poll(lhs_ty)
            && let TyKind::Reference(_re, _muta, pointee) = *lhs_ty.r(s)
        {
            self.overload_resolutions
                .insert(expr, OverloadResolution::Primitive);

            return pointee;
        }

        // Otherwise, attempt to perform an overloaded operation.
        if let Some(overload) = kind_info.overload {
            let result_ty = self.ccx_mut().fresh_ty_infer(
                HrtbUniverse::ROOT,
                InferTyVarSourceInfo::OverloadedResult {
                    span: expr.r(s).span,
                },
            );

            self.ccx_mut().oblige_ty_meets_trait_instantiated(
                cause,
                HrtbUniverse::ROOT,
                lhs_ty,
                TraitSpec {
                    def: overload,
                    params: tcx.intern_list(&[TraitParam::Equals(TyOrRe::Ty(result_ty))]),
                },
            );

            self.overload_resolutions
                .insert(expr, OverloadResolution::Call);

            return result_ty;
        }

        let error = fallback_err.report(self.ccx()).unwrap();

        self.overload_resolutions
            .insert(expr, OverloadResolution::Error(error));

        tcx.intern(TyKind::Error(error))
    }

    pub fn check_expr_inner_assign_op(
        &mut self,
        expr: Obj<HirExpr>,
        kind: AstAssignOpKind,
        lhs: Obj<HirPat>,
        rhs: Obj<HirExpr>,
        divergence: &mut Divergence,
    ) -> Ty {
        let tcx = self.tcx();
        let s = self.session();

        'assign: {
            let lhs = self.check_pat_infer(lhs, Some(divergence));
            let rhs = self.check_expr(rhs, None).and_do(divergence);

            let kind_info = self.decode_assign_op_kind(kind);
            let cause = ObligeCause::new_report(ObligeCauseOrigin::HirBodyCheckArithmetic {
                op_span: expr.r(s).span,
            });

            // Attempt a primitive operation.
            let mut prim_fork = self.ccx().clone();

            let fallback_err = 'try_prim: {
                let lhs = peel_ref_for_prim_op(&mut prim_fork, lhs);
                let rhs = peel_ref_for_prim_op(&mut prim_fork, rhs);

                if let Err(err) = prim_fork.unify_ty_and_simple_set(&cause, lhs, kind_info.lhs) {
                    break 'try_prim ClauseError::TyAndSimpleTySetUnifyError(err);
                }

                match kind_info.rhs {
                    EquateOrSet::EqualsLhs => {
                        if let Err(err) =
                            prim_fork.unify_ty_and_ty(&cause, lhs, rhs, RelationMode::Equate)
                        {
                            break 'try_prim ClauseError::TyAndTyUnifyError(*err);
                        }
                    }
                    EquateOrSet::Unrelated(rhs_set) => {
                        if let Err(err) = prim_fork.unify_ty_and_simple_set(&cause, lhs, rhs_set) {
                            break 'try_prim ClauseError::TyAndSimpleTySetUnifyError(err);
                        }
                    }
                }

                *self.ccx_mut() = prim_fork;
                break 'assign;
            };

            // Otherwise, attempt to perform an overloaded operation.
            if let Some(overload) = kind_info.overload {
                let result_ty = self.ccx_mut().fresh_ty_infer(
                    HrtbUniverse::ROOT,
                    InferTyVarSourceInfo::OverloadedResult {
                        span: expr.r(s).span,
                    },
                );

                self.ccx_mut().oblige_ty_meets_trait_instantiated(
                    cause,
                    HrtbUniverse::ROOT,
                    lhs,
                    TraitSpec {
                        def: overload,
                        params: tcx.intern_list(&[
                            TraitParam::Equals(TyOrRe::Ty(rhs)),
                            TraitParam::Equals(TyOrRe::Ty(result_ty)),
                        ]),
                    },
                );
            }

            fallback_err.report(&prim_fork);
        }

        tcx.intern(TyKind::Tuple(tcx.intern_list(&[])))
    }

    pub fn check_expr_inner_index(
        &mut self,
        expr: Obj<HirExpr>,
        target: Obj<HirExpr>,
        index: Obj<HirExpr>,
        divergence: &mut Divergence,
    ) -> Ty {
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

        self.ccx_mut().oblige_ty_meets_trait_instantiated(
            ObligeCause::new_report(ObligeCauseOrigin::HirBodyCheckIndex {
                target_span: target.r(s).span,
                index_span: index.r(s).span,
            }),
            HrtbUniverse::ROOT,
            target_ty,
            TraitSpec {
                def: index_trait,
                params: tcx.intern_list(&[
                    TraitParam::Equals(TyOrRe::Ty(index_ty)),
                    TraitParam::Equals(TyOrRe::Ty(output_ty)),
                ]),
            },
        );

        self.check_expr_demand(index, index_ty).and_do(divergence);

        output_ty
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
