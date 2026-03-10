use crate::{
    base::{
        Session,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    semantic::syntax::{
        GenericBinder, HirExpr, HirPat, ImplItem, Item, Mutability, SpannedTy, TraitItem, Ty,
        Visibility,
    },
};
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign};

// === FnItem === //

#[derive(Debug, Clone)]
pub struct FnItem {
    pub item: Obj<Item>,
    pub def: LateInit<Obj<FnDef>>,
}

#[derive(Debug, Clone)]
pub struct FnDef {
    pub span: Span,
    pub owner: LateInit<FnDefOwner>,
    pub name: Ident,
    pub impl_vis: Option<Visibility>,
    pub generics: Obj<GenericBinder>,
    pub has_self_param: LateInit<bool>,
    pub args: LateInit<Obj<[FnArg]>>,
    pub ret_ty: LateInit<SpannedTy>,
    pub body: LateInit<Option<Obj<HirExpr>>>,
}

#[derive(Debug, Copy, Clone)]
pub enum FnDefOwner {
    Item(Obj<FnItem>),
    TraitMethod(Obj<TraitItem>, u32),
    ImplMethod(Obj<ImplItem>, u32),
}

impl FnDefOwner {
    pub fn as_item(self, s: &Session) -> Obj<Item> {
        match self {
            FnDefOwner::Item(def) => def.r(s).item,
            FnDefOwner::TraitMethod(def, _) => def.r(s).item,
            FnDefOwner::ImplMethod(def, _) => def.r(s).item,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FnArg {
    pub span: Span,
    pub pat: Obj<HirPat>,
    pub ty: SpannedTy,
}

#[derive(Debug, Clone)]
pub struct FnLocal {
    pub mutability: Mutability,
    pub name: Ident,
}

// === Divergence === //

#[derive(Debug, Copy, Clone)]
#[must_use]
pub struct TyAndDivergence {
    pub ty: Ty,
    pub divergence: Divergence,
}

impl TyAndDivergence {
    pub const fn new(ty: Ty, divergence: Divergence) -> Self {
        Self { ty, divergence }
    }

    pub fn ignore(self) {
        // (empty)
    }

    pub fn and_do(self, divergence: &mut Divergence) -> Ty {
        *divergence &= self.divergence;
        self.ty
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum Divergence {
    MustDiverge,
    MayDiverge,
}

impl BitOr for Divergence {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Divergence::MustDiverge, Divergence::MustDiverge) => Divergence::MustDiverge,
            _ => Divergence::MayDiverge,
        }
    }
}

impl BitOrAssign for Divergence {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl BitAnd for Divergence {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Divergence::MayDiverge, Divergence::MayDiverge) => Divergence::MayDiverge,
            _ => Divergence::MustDiverge,
        }
    }
}

impl BitAndAssign for Divergence {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl Divergence {
    pub fn must_diverge(self) -> bool {
        matches!(self, Self::MustDiverge)
    }
}
