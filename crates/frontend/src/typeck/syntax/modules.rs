use crate::{
    base::{
        arena::{LateInit, Obj},
        syntax::{Span, Symbol},
    },
    parse::token::Ident,
    typeck::{
        lower::modules::{AnyDef, ParentKind},
        syntax::TraitDef,
    },
    utils::hash::FxIndexMap,
};

#[derive(Debug, Clone)]
pub struct Module {
    pub parent: ParentKind<Obj<Module>>,
    pub name: Option<Ident>,
    pub path: Symbol,
    pub direct_uses: LateInit<FxIndexMap<Symbol, DirectUse>>,
    pub glob_uses: LateInit<Vec<GlobUse>>,
}

#[derive(Debug, Clone)]
pub enum Visibility {
    Pub,
    PubIn(Obj<Module>),
}

#[derive(Debug, Clone)]
pub struct GlobUse {
    pub span: Span,
    pub visibility: Visibility,
    pub target: Obj<Module>,
}

#[derive(Debug, Clone)]
pub struct DirectUse {
    pub visibility: Visibility,
    pub target: AnyDef<Obj<Module>, Obj<Item>>,
}

#[derive(Debug, Clone)]
pub struct Item {
    pub parent: Obj<Module>,
    pub name: Ident,
    pub path: Symbol,
    pub kind: LateInit<ItemKind>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ItemKind {
    Trait(Obj<TraitDef>),
}
