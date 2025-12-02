use crate::{
    base::{
        arena::{LateInit, Obj},
        syntax::{Span, Symbol},
    },
    parse::token::Ident,
    semantic::{
        lower::modules::{ItemCategory, ParentRef},
        syntax::{AdtDef, FnItem, ImplDef, TraitDef},
    },
    utils::hash::FxIndexMap,
};

#[derive(Debug, Clone)]
pub struct Crate {
    pub name: Symbol,
    pub is_local: bool,
    pub root: LateInit<Obj<Item>>,
    pub items: LateInit<Vec<Obj<Item>>>,
}

#[derive(Debug, Clone)]
pub struct Item {
    pub krate: Obj<Crate>,
    pub direct_parent: ParentRef<Obj<Item>>,
    pub category: ItemCategory,
    pub name: Option<Ident>,
    pub path: Symbol,
    pub direct_uses: LateInit<FxIndexMap<Symbol, DirectUse>>,
    pub glob_uses: LateInit<Vec<GlobUse>>,
    pub kind: LateInit<ItemKind>,
}

#[derive(Debug, Clone)]
pub enum Visibility {
    Pub,
    PubIn(Obj<Item>),
}

#[derive(Debug, Clone)]
pub struct GlobUse {
    pub span: Span,
    pub visibility: Visibility,
    pub target: Obj<Item>,
}

#[derive(Debug, Clone)]
pub struct DirectUse {
    pub visibility: Visibility,
    pub target: Obj<Item>,
    pub is_direct_child: bool,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ItemKind {
    Module(Obj<Module>),
    Adt(Obj<AdtDef>),
    Trait(Obj<TraitDef>),
    Impl(Obj<ImplDef>),
    Func(Obj<FnItem>),
}

impl ItemKind {
    pub fn as_adt(self) -> Option<Obj<AdtDef>> {
        match self {
            ItemKind::Adt(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_trait(self) -> Option<Obj<TraitDef>> {
        match self {
            ItemKind::Trait(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_impl(self) -> Option<Obj<ImplDef>> {
        match self {
            ItemKind::Impl(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_func(self) -> Option<Obj<FnItem>> {
        match self {
            ItemKind::Func(v) => Some(v),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Module {
    pub item: Obj<Item>,
}
