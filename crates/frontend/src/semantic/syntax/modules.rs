use crate::{
    base::{
        Session,
        arena::{LateInit, Obj},
        syntax::{Span, Symbol},
    },
    parse::token::Ident,
    semantic::{
        lower::modules::{FrozenModuleResolver, ItemCategory, ItemPathFmt, ParentResolver as _},
        syntax::{
            AdtEnumVariant, AdtItem, AdtKindEnum, Attribute, FuncItem, ImplItem, LangItems,
            TraitItem, TypeAliasItem,
        },
    },
    symbol,
    utils::hash::FxIndexMap,
};
use derive_where::derive_where;

#[derive(Debug, Clone)]
pub struct Crate {
    pub name: Symbol,
    pub is_local: bool,
    pub root: LateInit<Obj<Item>>,
    pub items: LateInit<Vec<Obj<Item>>>,
    pub lang_items: LangItems,
}

#[derive_where(Debug)]
#[derive(Clone)]
pub struct Item {
    #[derive_where(skip)]
    pub krate: Obj<Crate>,
    #[derive_where(skip)]
    pub direct_parent: Option<Obj<Item>>,
    pub category: ItemCategory,
    pub name: Option<Ident>,
    pub path: Symbol,
    pub direct_uses: LateInit<FxIndexMap<Symbol, DirectUse>>,
    pub glob_uses: LateInit<Vec<GlobUse>>,
    pub attrs: LateInit<Vec<Obj<Attribute>>>,
    pub kind: LateInit<ItemKind>,
}

impl Item {
    pub fn display_path(&self, s: &Session) -> ItemPathFmt {
        ItemPathFmt {
            prefix: if self.krate.r(s).is_local {
                symbol!("crate")
            } else {
                self.krate.r(s).name
            },
            main_part: self.path,
        }
    }

    pub fn bare_category_path(&self, s: &Session) -> String {
        format!("{} `{}`", self.category.bare_what(), self.display_path(s))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Visibility {
    Pub,
    PubIn(Obj<Item>),
}

impl Visibility {
    pub fn is_visible_to(self, vis_ctxt: Obj<Item>, s: &Session) -> bool {
        match self {
            Visibility::Pub => true,
            Visibility::PubIn(vis_in) => FrozenModuleResolver(s).is_descendant(vis_ctxt, vis_in),
        }
    }
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
    Module(Obj<ModuleItem>),
    Adt(Obj<AdtItem>),
    EnumVariant(Obj<EnumVariantItem>),
    Trait(Obj<TraitItem>),
    Impl(Obj<ImplItem>),
    Func(Obj<FuncItem>),
    TypeAlias(Obj<TypeAliasItem>),
}

impl ItemKind {
    pub fn as_adt(self) -> Option<Obj<AdtItem>> {
        match self {
            ItemKind::Adt(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_enum_variant(self) -> Option<Obj<EnumVariantItem>> {
        match self {
            ItemKind::EnumVariant(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_trait(self) -> Option<Obj<TraitItem>> {
        match self {
            ItemKind::Trait(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_impl(self) -> Option<Obj<ImplItem>> {
        match self {
            ItemKind::Impl(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_func(self) -> Option<Obj<FuncItem>> {
        match self {
            ItemKind::Func(v) => Some(v),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct EnumVariantItem {
    pub item: Obj<Item>,
    pub owner: Obj<Item>,
    pub idx: u32,
}

impl EnumVariantItem {
    pub fn adt(&self, s: &Session) -> Obj<AdtItem> {
        self.owner.r(s).kind.as_adt().unwrap()
    }

    pub fn adt_as_enum(&self, s: &Session) -> Obj<AdtKindEnum> {
        self.adt(s).r(s).kind.as_enum().unwrap()
    }

    pub fn adt_variant(&self, s: &Session) -> Obj<AdtEnumVariant> {
        self.adt_as_enum(s).r(s).variants[self.idx as usize]
    }
}

#[derive(Debug, Clone)]
pub struct ModuleItem {
    pub item: Obj<Item>,
}
