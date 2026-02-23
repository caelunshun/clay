use crate::{
    base::{
        ErrorGuaranteed, Session,
        analysis::DebruijnRelative,
        arena::{HasInterner, Intern, LateInit, Obj},
        syntax::{Span, Symbol},
    },
    parse::token::{Ident, Lifetime},
    semantic::{
        analysis::TyCtxt,
        syntax::{
            FnDef, FnItem, Item, SpannedTraitClauseList, SpannedTraitInstance, SpannedTy,
            SpannedTyOrReList, Visibility,
        },
    },
    symbol,
    utils::hash::FxHashMap,
};
use derive_where::derive_where;
use index_vec::{IndexVec, define_index_type};
use smallvec::{SmallVec, smallvec};
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

#[derive(Debug, Copy, Clone)]
pub struct AdtCtorInstance {
    pub def: Obj<AdtCtor>,
    pub params: SpannedTyOrReList,
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

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct AdtInstance {
    pub def: Obj<AdtItem>,
    pub params: TyOrReList,
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

pub type ListOfTraitClauseList = Intern<[TraitClauseList]>;

/// A trait clause with multiple parts (e.g. `'a + Foo<u32> + Bar<Item = Baz>`).
pub type TraitClauseList = Intern<[TraitClause]>;

/// A single trait clause (e.g. `'a` or `Trait<'re1, Ty1, Ty2, AssocA = Ty3, AssocC = Ty4>`).
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TraitClause {
    Outlives(RelationDirection, TyOrRe),
    Trait(HrtbBinder<TraitSpec>),
}

pub type TraitParamList = Intern<[TraitParam]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TraitParam {
    Equals(TyOrRe),
    Unspecified(TraitClauseList),
}

// === Impls === //

#[derive(Debug, Clone)]
pub struct ImplItem {
    pub item: Obj<Item>,
    pub generics: Obj<GenericBinder>,
    pub trait_: LateInit<Option<SpannedTraitInstance>>,
    pub target: LateInit<SpannedTy>,
    pub methods: LateInit<Vec<Option<Obj<FnDef>>>>,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct TraitSpec {
    pub def: Obj<TraitItem>,
    pub params: TraitParamList,
}

impl fmt::Debug for TraitSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &Session::fetch();

        f.debug_struct("TraitSpec")
            .field("def", &self.def.r(s).item.r(s).name.unwrap().text)
            .field("params", &self.params)
            .finish()
    }
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct TraitInstance {
    pub def: Obj<TraitItem>,
    pub params: TyOrReList,
}

impl fmt::Debug for TraitInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &Session::fetch();

        f.debug_struct("TraitInstance")
            .field("def", &self.def.r(s).item.r(s).name.unwrap().text)
            .field("params", &self.params)
            .finish()
    }
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

// === Type === //

pub type TyOrReList = Intern<[TyOrRe]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TyOrReKind {
    Re,
    Ty,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TyOrRe {
    Re(Re),
    Ty(Ty),
}

impl TyOrRe {
    pub fn kind(self) -> TyOrReKind {
        match self {
            TyOrRe::Re(_) => TyOrReKind::Re,
            TyOrRe::Ty(_) => TyOrReKind::Ty,
        }
    }

    pub fn as_re(self) -> Option<Re> {
        match self {
            TyOrRe::Re(v) => Some(v),
            TyOrRe::Ty(_) => None,
        }
    }

    pub fn as_ty(self) -> Option<Ty> {
        match self {
            TyOrRe::Ty(v) => Some(v),
            TyOrRe::Re(_) => None,
        }
    }

    pub fn unwrap_re(self) -> Re {
        self.as_re().unwrap()
    }

    pub fn unwrap_ty(self) -> Ty {
        self.as_ty().unwrap()
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum Re {
    /// The top region type. Essentially, this pointer is either managed by the garbage collector or
    /// lives for the entire duration of the program.
    Gc,

    /// An uninstantiated request to infer the lifetime (e.g. `'_`).
    ///
    /// Used in user annotations and instantiated into an `InferVar` region during `ClauseCx`
    /// import.
    SigInfer,

    /// An uninstantiated generic lifetime parameter.
    ///
    /// Used in user annotations and instantiated into either a `UniversalVar`, an `InferVar`, or if
    /// bound within an HRTB binder, a `HrtbVar` during `ClauseCx` import.
    SigGeneric(Obj<RegionGeneric>),

    /// An instantiated generic region variable within an HRTB binder (e.g. the `'a` in the type
    /// `Foo<'a>` in the clause `for<'a> Foo<'a>`).
    ///
    /// This is first instantiated from a `SigGeneric within an HRTB binder. Similar to a
    /// `SigGeneric`, it is later instantiated into a `UniversalVar` or an `InferVar` during trait
    /// obligation checking depending on how the HRTB is being used.
    ///
    /// These are indexed using debruijn indices.
    HrtbVar(HrtbDebruijn),

    /// An internal lifetime parameter within the body.
    InferVar(InferReVar),

    /// An instantiated generic lifetime parameter.
    UniversalVar(UniversalReVar),

    /// The lifetime used when we don't want to worry about lifetimes.
    Erased,

    Error(ErrorGuaranteed),
}

pub type Ty = Intern<TyKind>;
pub type TyList = Intern<[Ty]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TyKind {
    /// The `Self`-type.
    ///
    /// Used in user annotations and instantiated into the actual `Self` type during `ClauseCx`
    /// import.
    SigThis,

    /// An uninstantiated request to infer a type (e.g. `_`).
    ///
    /// Used in user annotations and instantiated into an `InferVar` type during `ClauseCx`
    /// import.
    SigInfer,

    /// An uninstantiated generic type parameter.
    ///
    /// Used in user annotations and instantiated into either a `UniversalVar`, an `InferVar`, or if
    /// bound within an HRTB binder, a `HrtbVar` during `ClauseCx` import.
    SigGeneric(Obj<TypeGeneric>),

    /// An uninstantiated type projection, which fetches an associated type from a `trait` impl for
    /// the given type.
    ///
    /// Used in user annotations and instantiated into an `InferVar` which is used in a trait
    /// obligation to constrain the inference variable to its target associated type.
    SigProject(TyProjection),

    /// An uninstantiated type alias. Resolved at import time.
    SigAlias(Obj<TypeAliasItem>, TyOrReList),

    /// A simple primitive non-composite type living for `'gc`.
    Simple(SimpleTyKind),

    /// A reference type.
    Reference(Re, Mutability, Ty),

    /// An instantiation of an ADT.
    Adt(AdtInstance),

    /// A `&'re dyn Trait` object.
    Trait(Re, Mutability, TraitClauseList),

    /// A tuple.
    Tuple(TyList),

    /// A statically-known function type. This can be coerced into a functional interface.
    FnDef(FnInstance),

    /// An instantiated generic region variable within an HRTB binder (e.g. the `T` in the type
    /// `Foo<T>` in the clause `for<T> Foo<T>`).
    ///
    /// This is first instantiated from a `SigGeneric within an HRTB binder. Similar to a
    /// `SigGeneric`, it is later instantiated into a `UniversalVar` or an `InferVar` during trait
    /// obligation checking depending on how the HRTB is being used.
    ///
    /// These are indexed using debruijn indices.
    HrtbVar(HrtbDebruijn),

    /// An inference variable.
    InferVar(InferTyVar),

    /// An universal type variable.
    UniversalVar(UniversalTyVar),

    Error(ErrorGuaranteed),
}

pub type FnInstance = Intern<FnInstanceInner>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct FnInstanceInner {
    pub owner: FnOwner,

    /// If the user provides an explicit set of generic arguments to a function, this will be
    /// `Some`. Otherwise, the function is allowed to range over all generic instantiations of that
    /// function.
    pub early_args: Option<TyOrReList>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum FnOwner {
    Item(Obj<FnItem>),
    Trait {
        instance: TraitSpec,
        self_ty: Ty,
        method_idx: u32,
    },
    Inherent {
        self_ty: Ty,
        block: Obj<ImplItem>,
        method_idx: u32,
    },
}

impl FnOwner {
    pub fn def(self, s: &Session) -> Obj<FnDef> {
        match self {
            FnOwner::Item(def) => *def.r(s).def,
            FnOwner::Trait {
                instance,
                self_ty: _,
                method_idx,
            } => instance.def.r(s).methods[method_idx as usize],
            FnOwner::Inherent {
                self_ty: _,
                block,
                method_idx,
            } => block.r(s).methods[method_idx as usize].unwrap(),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct TyProjection {
    pub target: Ty,
    pub spec: TraitSpec,
    pub assoc: u32,
}

define_index_type! {
    pub struct InferReVar = u32;
}

define_index_type! {
    pub struct InferTyVar = u32;
}

define_index_type! {
    pub struct UniversalTyVar = u32;
}

define_index_type! {
    pub struct UniversalReVar = u32;
}

bitflags::bitflags! {
    #[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
    pub struct SimpleTySet: u16 {
        const OTHER = 1 << 0;
        const U8 = 1 << 1;
        const U16 = 1 << 2;
        const U32 = 1 << 3;
        const U64 = 1 << 4;
        const I8 = 1 << 5;
        const I16 = 1 << 6;
        const I32 = 1 << 7;
        const I64 = 1 << 8;
        const F32 = 1 << 9;
        const F64 = 1 << 10;

        // Not used for inference. We just reuse the `InferTyPermSet` machinery to simplify
        // arithmetic checking.
        const BOOL = 1 << 11;
        const CHAR = 1 << 12;

        const UNSIGNED_INT = Self::U8.bits() | Self::U16.bits() | Self::U32.bits() | Self::U64.bits();
        const SIGNED_INT = Self::I8.bits() | Self::I16.bits() | Self::I32.bits() | Self::I64.bits();
        const INT = Self::UNSIGNED_INT.bits() | Self::SIGNED_INT.bits();
        const FLOAT = Self::F32.bits() | Self::F64.bits();
        const NUM = Self::INT.bits() | Self::FLOAT.bits();
        const SIGNED_NUM = Self::SIGNED_INT.bits() | Self::FLOAT.bits();
    }
}

impl SimpleTySet {
    pub fn can_accept_type(self, ty: Ty, s: &Session) -> bool {
        match *ty.r(s) {
            TyKind::SigThis
            | TyKind::SigInfer
            | TyKind::SigGeneric(_)
            | TyKind::SigProject(_)
            | TyKind::SigAlias(_, _) => unreachable!(),

            TyKind::Simple(SimpleTyKind::Uint(IntKind::S8)) => self.contains(SimpleTySet::U8),
            TyKind::Simple(SimpleTyKind::Uint(IntKind::S16)) => self.contains(SimpleTySet::U16),
            TyKind::Simple(SimpleTyKind::Uint(IntKind::S32)) => self.contains(SimpleTySet::U32),
            TyKind::Simple(SimpleTyKind::Uint(IntKind::S64)) => self.contains(SimpleTySet::U64),
            TyKind::Simple(SimpleTyKind::Int(IntKind::S8)) => self.contains(SimpleTySet::I8),
            TyKind::Simple(SimpleTyKind::Int(IntKind::S16)) => self.contains(SimpleTySet::I16),
            TyKind::Simple(SimpleTyKind::Int(IntKind::S32)) => self.contains(SimpleTySet::I32),
            TyKind::Simple(SimpleTyKind::Int(IntKind::S64)) => self.contains(SimpleTySet::I64),
            TyKind::Simple(SimpleTyKind::Float(FloatKind::S32)) => self.contains(SimpleTySet::F32),
            TyKind::Simple(SimpleTyKind::Float(FloatKind::S64)) => self.contains(SimpleTySet::F64),

            TyKind::Reference(_, _, _)
            | TyKind::Adt(_)
            | TyKind::Trait(_, _, _)
            | TyKind::Tuple(_)
            | TyKind::FnDef(_)
            | TyKind::HrtbVar(_)
            | TyKind::UniversalVar(_)
            | TyKind::Simple(
                SimpleTyKind::Bool | SimpleTyKind::Char | SimpleTyKind::Str | SimpleTyKind::Never,
            ) => self.contains(SimpleTySet::OTHER),

            TyKind::InferVar(_) | TyKind::Error(_) => unreachable!(),
        }
    }

    pub fn to_unique_type(self, tcx: &TyCtxt) -> Option<Ty> {
        (self.iter().count() == 1)
            .then(|| match self.iter().next().unwrap() {
                SimpleTySet::INT => None,
                SimpleTySet::U8 => Some(SimpleTyKind::Uint(IntKind::S8)),
                SimpleTySet::U16 => Some(SimpleTyKind::Uint(IntKind::S16)),
                SimpleTySet::U32 => Some(SimpleTyKind::Uint(IntKind::S32)),
                SimpleTySet::U64 => Some(SimpleTyKind::Uint(IntKind::S64)),
                SimpleTySet::I8 => Some(SimpleTyKind::Int(IntKind::S8)),
                SimpleTySet::I16 => Some(SimpleTyKind::Int(IntKind::S16)),
                SimpleTySet::I32 => Some(SimpleTyKind::Int(IntKind::S32)),
                SimpleTySet::I64 => Some(SimpleTyKind::Int(IntKind::S64)),
                SimpleTySet::F32 => Some(SimpleTyKind::Float(FloatKind::S32)),
                SimpleTySet::F64 => Some(SimpleTyKind::Float(FloatKind::S64)),

                _ => unreachable!(),
            })
            .flatten()
            .map(|kind| tcx.intern(TyKind::Simple(kind)))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum UniversalReVarSourceInfo {
    Root(Obj<RegionGeneric>),
    ElaboratedLub,
    HrtbVar,
    TestPlaceholder,
}

#[derive(Debug, Copy, Clone)]
pub enum UniversalTyVarSourceInfo {
    TraitSelf,
    HrtbVar,
    Root(Obj<TypeGeneric>),
    Projection(UniversalTyVar, TraitSpec, u32),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum SimpleTyKind {
    Never,
    Bool,
    Char,
    Int(IntKind),
    Uint(IntKind),
    Float(FloatKind),
    Str,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum IntKind {
    S8,
    S16,
    S32,
    S64,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum FloatKind {
    S32,
    S64,
}

// === Coherence === //

pub type TyShapeList = Intern<[TyShape]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TyShape {
    Hole,
    Solid(SolidTyShape),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SolidTyShape {
    pub kind: SolidTyShapeKind,
    pub children: TyShapeList,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum SolidTyShapeKind {
    /// A top-level coherence type indicating the implementation of a trait.
    ///
    /// The type's children are organized into two parts:
    ///
    /// - The first child is the target type.
    /// - The remaining `trait_def.regular_generic_count` child types (minus the number of region
    ///   generics) represent the trait arguments.
    ///
    TraitImpl(Obj<TraitItem>),

    /// A top-level coherence type indicating the implementation of a specific method in an inherent
    /// `impl` block. This type has exactly one child type indicating the *receiver target*.
    InherentMethodImpl(Symbol),

    /// A top-level coherence type indicating the implementation of a specific associated function
    /// in an inherent `impl` block. This type has exactly one child type indicating the *self
    /// type*.
    InherentFunctionImpl(Symbol),

    Simple(SimpleTyKind),
    Re(Mutability),
    Adt(Obj<AdtItem>),
    Trait,
    Tuple(u32),

    /// No need to specialize in an efficient manner because `impl`s naming these types are not
    /// possible.
    FnDef,
}

// === Binders === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct HrtbBinder<T> {
    pub kind: HrtbBinderKind,
    pub inner: T,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum HrtbBinderKind {
    Signature(Obj<GenericBinder>),
    Imported(HrtbDebruijnDefList),
}

pub type HrtbDebruijnDefList = Intern<[HrtbDebruijnDef]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct HrtbDebruijnDef {
    pub spawned_from: Span,
    pub kind: TyOrReKind,
    pub clauses: TraitClauseList,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct HrtbDebruijn(pub DebruijnRelative);

// === Misc Enums === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ReVariance {
    Invariant,
    Covariant,
    Contravariant,
}

impl ReVariance {
    pub fn rev(self) -> Self {
        match self {
            ReVariance::Invariant => ReVariance::Invariant,
            ReVariance::Covariant => ReVariance::Contravariant,
            ReVariance::Contravariant => ReVariance::Covariant,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum RelationDirection {
    LhsOntoRhs,
    RhsOntoLhs,
}

impl RelationDirection {
    #[must_use]
    pub fn to_mode(self) -> RelationMode {
        match self {
            RelationDirection::LhsOntoRhs => RelationMode::LhsOntoRhs,
            RelationDirection::RhsOntoLhs => RelationMode::RhsOntoLhs,
        }
    }

    #[must_use]
    pub fn invert(self) -> RelationDirection {
        match self {
            RelationDirection::LhsOntoRhs => RelationDirection::RhsOntoLhs,
            RelationDirection::RhsOntoLhs => RelationDirection::LhsOntoRhs,
        }
    }

    pub fn adapt<T: Copy>(self, lhs: T, rhs: T) -> (T, T) {
        match self {
            RelationDirection::LhsOntoRhs => (lhs, rhs),
            RelationDirection::RhsOntoLhs => (rhs, lhs),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum RelationMode {
    LhsOntoRhs,
    RhsOntoLhs,
    Equate,
}

impl RelationMode {
    #[must_use]
    pub fn with_variance(self, variance: ReVariance) -> RelationMode {
        match variance {
            ReVariance::Invariant => RelationMode::Equate,
            ReVariance::Covariant => self,
            ReVariance::Contravariant => self.invert(),
        }
    }

    #[must_use]
    pub fn invert(self) -> RelationMode {
        match self {
            RelationMode::LhsOntoRhs => RelationMode::RhsOntoLhs,
            RelationMode::RhsOntoLhs => RelationMode::LhsOntoRhs,
            RelationMode::Equate => RelationMode::Equate,
        }
    }

    pub fn enumerate<T: Copy>(self, lhs: T, rhs: T) -> SmallVec<[(T, T); 2]> {
        match self {
            RelationMode::LhsOntoRhs => smallvec![(lhs, rhs)],
            RelationMode::RhsOntoLhs => smallvec![(rhs, lhs)],
            RelationMode::Equate => smallvec![(lhs, rhs), (rhs, lhs)],
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum Mutability {
    Not,
    Mut,
}

impl Mutability {
    pub fn adverb(self) -> Symbol {
        match self {
            Mutability::Mut => symbol!("mutably"),
            Mutability::Not => symbol!("immutably"),
        }
    }
}
