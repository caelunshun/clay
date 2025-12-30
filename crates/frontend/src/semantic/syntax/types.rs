use crate::{
    base::{
        ErrorGuaranteed, Session,
        arena::{Intern, LateInit, Obj},
        syntax::{Span, Symbol},
    },
    parse::token::{Ident, Lifetime},
    semantic::syntax::{
        FnDef, Item, SpannedTraitClauseList, SpannedTraitInstance, SpannedTy, SpannedTyOrReList,
        Visibility,
    },
    symbol,
    utils::hash::FxHashMap,
};
use derive_where::derive_where;
use index_vec::define_index_type;
use std::fmt;

// === Adt Items === //

#[derive(Debug, Clone)]
pub struct AdtItem {
    pub item: Obj<Item>,
    pub generics: Obj<GenericBinder>,
    pub kind: LateInit<AdtKind>,
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
    pub variants: LateInit<Vec<Obj<AdtEnumVariant>>>,
    pub by_name: LateInit<FxHashMap<Symbol, u32>>,
}

#[derive(Debug, Clone)]
pub struct AdtEnumVariant {
    pub owner: Obj<AdtKindEnum>,
    pub span: Span,
    pub idx: u32,
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

#[derive(Debug, Clone)]
pub struct AdtCtor {
    pub owner: AdtCtorOwner,
    pub syntax: AdtCtorSyntax,
    pub fields: Vec<AdtCtorField>,
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
    Named(FxHashMap<Symbol, u32>),
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

    pub fn unwrap_names(&self) -> &FxHashMap<Symbol, u32> {
        match self {
            AdtCtorSyntax::Named(v) => v,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct AdtCtorField {
    pub span: Span,
    pub idx: u32,
    pub vis: Visibility,
    pub ident: Option<Ident>,
    pub ty: LateInit<SpannedTy>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct AdtInstance {
    pub def: Obj<AdtItem>,
    pub params: TyOrReList,
}

// === Traits === //

#[derive(Debug, Clone)]
pub struct TraitItem {
    /// The item defining this trait.
    pub item: Obj<Item>,

    /// The set of parameter generics and associated types defined by this trait. This list starts
    /// with a `regular_generic_count` number of generic parameters followed by associated types.
    pub generics: Obj<GenericBinder>,

    /// The set of traits inherited by the current trait.
    pub inherits: LateInit<SpannedTraitClauseList>,

    /// The number of generic parameters taken by this trait.
    pub regular_generic_count: u32,

    /// Maps associated type names to their generic parameter as bound in `generics`.
    pub associated_types: FxHashMap<Symbol, Obj<TypeGeneric>>,

    /// The set of methods defined by this trait.
    pub methods: LateInit<Vec<Obj<TraitMethod>>>,
}

#[derive(Debug, Clone)]
pub struct TraitMethod {
    pub owner: Obj<TraitItem>,
    pub func: Obj<FnDef>,
}

pub type ListOfTraitClauseList = Intern<[TraitClauseList]>;

/// A trait clause with multiple parts (e.g. `'a + Foo<u32> + Bar<Item = Baz>`).
pub type TraitClauseList = Intern<[TraitClause]>;

/// A single trait clause (e.g. `'a` or `Trait<'re1, Ty1, Ty2, AssocA = Ty3, AssocC = Ty4>`).
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TraitClause {
    Outlives(Re),
    Trait(TraitSpec),
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
    pub trait_: Option<SpannedTraitInstance>,
    pub target: SpannedTy,
    pub methods: LateInit<Vec<Obj<FnDef>>>,
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
pub enum TyOrRe {
    Re(Re),
    Ty(Ty),
}

impl TyOrRe {
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

    /// Refers to a generic lifetime parameter.
    ///
    /// Used in user annotations and instantiated into either a `UniversalVar` or an `InferVar`
    /// region during `ClauseCx` import.
    SigGeneric(Obj<RegionGeneric>),

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
    /// Used in user annotations and instantiated into an `InferVar` region during `ClauseCx`
    /// import.
    SigInfer,

    /// The universal type quantification produced by a generic parameter.
    ///
    /// Used in user annotations and instantiated into either a `UniversalVar` or an `InferVar` type
    /// during `ClauseCx` import.
    SigGeneric(Obj<TypeGeneric>),

    /// A simple primitive non-composite type living for `'gc`.
    Simple(SimpleTyKind),

    /// A reference type.
    Reference(Re, Mutability, Ty),

    /// An instantiation of an ADT.
    Adt(AdtInstance),

    /// A `dyn Trait` object.
    Trait(TraitClauseList),

    /// A tuple.
    Tuple(TyList),

    /// A statically-known function type. This can be coerced into a functional interface.
    FnDef(Obj<FnDef>, Option<TyOrReList>),

    /// An inference variable.
    InferVar(InferTyVar),

    /// An universal type variable.
    UniversalVar(UniversalTyVar),

    Error(ErrorGuaranteed),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct InferReVar(pub u32);

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct InferTyVar(pub u32);

define_index_type! {
    pub struct UniversalTyVar = u32;
}

define_index_type! {
    pub struct UniversalReVar = u32;
}

#[derive(Debug, Copy, Clone)]
pub enum UniversalReVarSourceInfo {
    Root(Obj<RegionGeneric>),
    ElaboratedLub,
}

#[derive(Debug, Copy, Clone)]
pub enum UniversalTyVarSourceInfo {
    TraitSelf,
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
    S128,
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
    /// `impl` block. This type has exactly one child type indicating the implementation target.
    InherentMethodImpl(Symbol),

    Simple(SimpleTyKind),
    Re(Mutability),
    Adt(Obj<AdtItem>),
    Trait,
    Tuple(u32),
    FnDef,
}

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
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum Mutability {
    Mut,
    Not,
}

impl Mutability {
    pub fn adverb(self) -> Symbol {
        match self {
            Mutability::Mut => symbol!("mutably"),
            Mutability::Not => symbol!("immutably"),
        }
    }
}
