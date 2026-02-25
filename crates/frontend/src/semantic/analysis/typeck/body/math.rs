use crate::{
    base::arena::{HasInterner, Obj},
    parse::ast::{AstAssignOpKind, AstBinOpKind, AstUnOpKind},
    semantic::{
        analysis::{BodyCtxt, ClauseCx},
        syntax::{SimpleTyKind, SimpleTySet, TraitItem, Ty, TyKind},
    },
};

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
