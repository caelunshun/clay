use crate::{
    base::{
        Session,
        arena::{LateInit, Obj},
        syntax::{Span, Symbol},
    },
    parse::token::{Ident, Lifetime},
    semantic::{
        lower::func::path::TypeRelativeAssoc,
        syntax::{
            EnumVariantItem, FnDef, Item, SpannedTraitClauseList, SpannedTraitInstance,
            SpannedTraitSpec, SpannedTy, SpannedTyOrReList, TyOrReKind, TyOrReList, Visibility,
        },
    },
    symbol,
    utils::hash::FxHashMap,
};
use derive_where::derive_where;
use index_vec::{IndexVec, define_index_type};
use std::fmt;

// === Adt Items === //

#[derive(Clone)]
pub struct AdtItem {
    pub item: Obj<Item>,
    pub generics: Obj<GenericBinder>,
    pub kind: LateInit<AdtKind>,
}

impl fmt::Debug for AdtItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("AdtItem")
            .field(&self.item.r(&Session::fetch()).path)
            .finish()
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AdtKind {
    Struct(Obj<AdtKindStruct>),
    Enum(Obj<AdtKindEnum>),
}

impl AdtKind {
    pub fn as_enum(self) -> Option<Obj<AdtKindEnum>> {
        match self {
            AdtKind::Enum(def) => Some(def),
            AdtKind::Struct(_) => None,
        }
    }

    pub fn as_struct(self) -> Option<Obj<AdtKindStruct>> {
        match self {
            AdtKind::Struct(def) => Some(def),
            AdtKind::Enum(_) => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AdtKindStruct {
    pub adt: Obj<AdtItem>,
    pub ctor: LateInit<Obj<AdtCtor>>,
}

#[derive(Debug, Clone)]
pub struct AdtKindEnum {
    pub adt: Obj<AdtItem>,
    pub variants: LateInit<IndexVec<AdtEnumVariantIdx, Obj<AdtEnumVariant>>>,
    pub by_name: LateInit<FxHashMap<Symbol, AdtEnumVariantIdx>>,
}

define_index_type! {
    pub struct AdtEnumVariantIdx = u32;
}

#[derive(Debug, Clone)]
pub struct AdtEnumVariant {
    pub owner: Obj<AdtKindEnum>,
    pub span: Span,
    pub idx: AdtEnumVariantIdx,
    pub ident: Ident,
    pub ctor: LateInit<Obj<AdtCtor>>,
}

// === Adt Constructor === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AdtCtorOwner {
    Struct(Obj<AdtKindStruct>),
    EnumVariant(Obj<AdtEnumVariant>),
}

impl AdtCtorOwner {
    pub fn bare_identified_what(self, s: &Session) -> String {
        match self {
            AdtCtorOwner::Struct(struct_) => {
                format!(
                    "struct `{}`",
                    struct_.r(s).adt.r(s).item.r(s).display_path(s),
                )
            }
            AdtCtorOwner::EnumVariant(variant) => format!(
                "enum variant `{}::{}`",
                variant.r(s).owner.r(s).adt.r(s).item.r(s).display_path(s),
                variant.r(s).ident.text,
            ),
        }
    }

    pub fn bare_whats(self) -> Symbol {
        match self {
            AdtCtorOwner::Struct(..) => symbol!("`struct`s"),
            AdtCtorOwner::EnumVariant(..) => symbol!("`enum` variants"),
        }
    }
}

define_index_type! {
    pub struct AdtCtorFieldIdx = u32;
}

#[derive(Debug, Clone)]
pub struct AdtCtor {
    pub owner: AdtCtorOwner,
    pub syntax: AdtCtorSyntax,
    pub fields: IndexVec<AdtCtorFieldIdx, AdtCtorField>,
}

#[derive(Debug, Clone)]
pub enum AdtCtorSyntax {
    Unit,
    Tuple,
    Named(FxHashMap<Symbol, AdtCtorFieldIdx>),
}

impl AdtCtorSyntax {
    #[must_use]
    pub fn is_unit(&self) -> bool {
        matches!(self, AdtCtorSyntax::Unit)
    }

    #[must_use]
    pub fn is_tuple(&self) -> bool {
        matches!(self, AdtCtorSyntax::Tuple)
    }

    #[must_use]
    pub fn is_named(&self) -> bool {
        matches!(self, AdtCtorSyntax::Named(..))
    }

    pub fn unwrap_names(&self) -> &FxHashMap<Symbol, AdtCtorFieldIdx> {
        match self {
            AdtCtorSyntax::Named(v) => v,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct AdtCtorField {
    pub span: Span,
    pub idx: AdtCtorFieldIdx,
    pub vis: Visibility,
    pub ident: Option<Ident>,
    pub ty: LateInit<SpannedTy>,
}

#[derive(Debug, Copy, Clone)]
pub enum AdtCtorUnresolved {
    ResolvedTy(SpannedTy),
    ResolvedEnumVariant(Obj<EnumVariantItem>, SpannedTyOrReList),
    TypeRelative {
        self_ty: SpannedTy,
        as_trait: Option<SpannedTraitSpec>,
        assoc: TypeRelativeAssoc,
    },
}

#[derive(Debug, Copy, Clone)]
pub struct AdtCtorInstance {
    pub span: Span,
    pub def: Obj<AdtCtor>,
    pub params: SpannedTyOrReList,
}

// === Type Aliases === //

#[derive(Debug, Clone)]
pub struct TypeAliasItem {
    /// The item defining this trait.
    pub item: Obj<Item>,

    /// The set of parameter generics and associated types defined by this type alias.
    pub generics: Obj<GenericBinder>,

    /// The body to which the type is expanded.
    pub body: LateInit<SpannedTy>,
}

// === Traits === //

#[derive(Debug, Clone)]
pub struct TraitItem {
    /// The item defining this trait.
    pub item: Obj<Item>,

    /// The set of parameter generics and associated types defined by this trait. This list starts
    /// with a `regular_generic_count` number of generic parameters followed by associated types.
    pub generics: LateInit<Obj<GenericBinder>>,

    /// The set of traits inherited by the current trait.
    pub inherits: LateInit<SpannedTraitClauseList>,

    /// The number of generic parameters taken by this trait.
    pub regular_generic_count: LateInit<u32>,

    /// Maps associated type names to their generic parameter as bound in `generics`.
    pub associated_types: LateInit<FxHashMap<Symbol, Obj<TypeGeneric>>>,

    /// The set of methods defined by this trait.
    pub methods: LateInit<Vec<Obj<FnDef>>>,

    /// A map from method names to index.
    pub name_to_method: LateInit<FxHashMap<Symbol, u32>>,
}

#[derive(Debug, Clone)]
pub struct ImplItem {
    pub item: Obj<Item>,
    pub generics: Obj<GenericBinder>,
    pub trait_: LateInit<Option<SpannedTraitInstance>>,
    pub target: LateInit<SpannedTy>,
    pub methods: LateInit<Vec<Option<Obj<FnDef>>>>,
}

// === Generics === //

/// A container for a list of generics which can be substituted all at once.
#[derive(Debug, Clone, Default)]
pub struct GenericBinder {
    pub defs: Vec<AnyGeneric>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AnyGeneric {
    Re(Obj<RegionGeneric>),
    Ty(Obj<TypeGeneric>),
}

impl AnyGeneric {
    pub fn kind(self) -> TyOrReKind {
        match self {
            AnyGeneric::Re(_) => TyOrReKind::Re,
            AnyGeneric::Ty(_) => TyOrReKind::Ty,
        }
    }

    pub fn as_re(self) -> Option<Obj<RegionGeneric>> {
        match self {
            AnyGeneric::Re(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_ty(self) -> Option<Obj<TypeGeneric>> {
        match self {
            AnyGeneric::Ty(v) => Some(v),
            _ => None,
        }
    }

    pub fn unwrap_re(self) -> Obj<RegionGeneric> {
        self.as_re().unwrap()
    }

    pub fn unwrap_ty(self) -> Obj<TypeGeneric> {
        self.as_ty().unwrap()
    }

    pub fn binder(self, s: &Session) -> PosInBinder {
        match self {
            AnyGeneric::Re(re) => *re.r(s).binder,
            AnyGeneric::Ty(ty) => *ty.r(s).binder,
        }
    }

    pub fn clauses(self, s: &Session) -> SpannedTraitClauseList {
        match self {
            AnyGeneric::Re(re) => *re.r(s).clauses,
            AnyGeneric::Ty(ty) => *ty.r(s).clauses,
        }
    }

    pub fn span(self, s: &Session) -> Span {
        match self {
            AnyGeneric::Re(v) => v.r(s).span,
            AnyGeneric::Ty(v) => v.r(s).span,
        }
    }
}

#[derive_where(Debug)]
#[derive(Clone)]
pub struct RegionGeneric {
    #[derive_where(skip)]
    pub span: Span,
    pub lifetime: Lifetime,
    #[derive_where(skip)]
    pub binder: LateInit<PosInBinder>,
    pub clauses: LateInit<SpannedTraitClauseList>,
}

#[derive_where(Debug)]
#[derive(Clone)]
pub struct TypeGeneric {
    #[derive_where(skip)]
    pub span: Span,
    pub ident: Ident,
    #[derive_where(skip)]
    pub binder: LateInit<PosInBinder>,
    pub clauses: LateInit<SpannedTraitClauseList>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct PosInBinder {
    pub def: Obj<GenericBinder>,
    pub idx: u32,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct GenericSubst {
    pub binder: Obj<GenericBinder>,
    pub substs: TyOrReList,
}
