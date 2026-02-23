use crate::{
    base::arena::Obj,
    parse::ast::{AstBinOpKind, AstUnOpKind},
    semantic::{
        analysis::BodyCtxt,
        syntax::{SimpleTySet, TraitItem},
    },
};

#[derive(Debug, Copy, Clone)]
pub struct TypedOperation {
    pub prim_types: SimpleTySet,
    pub overload_trait: Option<Obj<TraitItem>>,
}

impl BodyCtxt<'_, '_> {
    pub fn decode_bin_op_kind(&self, op: AstBinOpKind) -> TypedOperation {
        let s = self.session();
        let lang_items = &self.krate().r(s).lang_items;

        match op {
            AstBinOpKind::Add => TypedOperation {
                prim_types: SimpleTySet::NUM,
                overload_trait: lang_items.add_trait(),
            },
            AstBinOpKind::Sub => TypedOperation {
                prim_types: SimpleTySet::NUM,
                overload_trait: lang_items.sub_trait(),
            },
            AstBinOpKind::Mul => TypedOperation {
                prim_types: SimpleTySet::NUM,
                overload_trait: lang_items.mul_trait(),
            },
            AstBinOpKind::Div => TypedOperation {
                prim_types: SimpleTySet::NUM,
                overload_trait: lang_items.div_trait(),
            },
            AstBinOpKind::Rem => TypedOperation {
                prim_types: SimpleTySet::NUM,
                overload_trait: lang_items.rem_trait(),
            },
            AstBinOpKind::And | AstBinOpKind::Or => TypedOperation {
                prim_types: SimpleTySet::BOOL,
                overload_trait: None,
            },
            AstBinOpKind::BitXor => TypedOperation {
                prim_types: SimpleTySet::INT | SimpleTySet::BOOL,
                overload_trait: lang_items.bit_xor_trait(),
            },
            AstBinOpKind::BitAnd => TypedOperation {
                prim_types: SimpleTySet::INT | SimpleTySet::BOOL,
                overload_trait: lang_items.bit_and_trait(),
            },
            AstBinOpKind::BitOr => TypedOperation {
                prim_types: SimpleTySet::INT | SimpleTySet::BOOL,
                overload_trait: lang_items.bit_or_trait(),
            },
            AstBinOpKind::Shl => TypedOperation {
                prim_types: SimpleTySet::INT,
                overload_trait: lang_items.bit_shl_trait(),
            },
            AstBinOpKind::Shr => TypedOperation {
                prim_types: SimpleTySet::INT,
                overload_trait: lang_items.bit_shr_trait(),
            },
            AstBinOpKind::Eq => TypedOperation {
                prim_types: SimpleTySet::NUM | SimpleTySet::BOOL,
                overload_trait: lang_items.partial_eq_trait(),
            },
            AstBinOpKind::Lt
            | AstBinOpKind::Le
            | AstBinOpKind::Ne
            | AstBinOpKind::Ge
            | AstBinOpKind::Gt => TypedOperation {
                prim_types: SimpleTySet::NUM,
                overload_trait: lang_items.ord_trait(),
            },
        }
    }

    pub fn for_un_op_kind(&self, op: AstUnOpKind) -> TypedOperation {
        let s = self.session();
        let lang_items = &self.krate().r(s).lang_items;

        match op {
            AstUnOpKind::Deref => TypedOperation {
                prim_types: SimpleTySet::empty(),
                overload_trait: lang_items.deref_trait(),
            },
            AstUnOpKind::Not => TypedOperation {
                prim_types: SimpleTySet::INT | SimpleTySet::BOOL,
                overload_trait: lang_items.not_trait(),
            },
            AstUnOpKind::Neg => TypedOperation {
                prim_types: SimpleTySet::SIGNED_NUM,
                overload_trait: lang_items.neg_trait(),
            },
        }
    }
}
