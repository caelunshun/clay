use crate::{
    base::{
        ErrorGuaranteed, Session,
        arena::{Intern, LateInit, Obj},
        syntax::{Span, Symbol},
    },
    parse::token::{Ident, Lifetime},
    semantic::syntax::{
        FnDef, Item, SpannedTraitClauseList, SpannedTraitInstance, SpannedTy, Visibility,
    },
    symbol,
    utils::hash::FxHashMap,
};
use derive_where::derive_where;
use std::fmt;

// === AdtDef === //

#[derive(Debug, Clone)]
pub struct AdtDef {
    pub item: Obj<Item>,
    pub generics: Obj<GenericBinder>,
    pub kind: AdtKind,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AdtKind {
    Enum(Obj<AdtKindEnum>),
    Struct(Obj<AdtKindStruct>),
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
pub struct AdtKindEnum {
    pub variants: Vec<AdtEnumVariant>,
    pub by_name: FxHashMap<Symbol, u32>,
}

#[derive(Debug, Clone)]
pub struct AdtEnumVariant {
    pub idx: u32,
    pub span: Span,
    pub ident: Ident,
    pub kind: Obj<AdtKindStruct>,
}

#[derive(Debug, Clone)]
pub struct AdtKindStruct {
    pub syntax: AdtStructFieldSyntax,
    pub fields: Vec<AdtStructField>,
}

#[derive(Debug, Clone)]
pub enum AdtStructFieldSyntax {
    Unit,
    Tuple,
    Named(FxHashMap<Symbol, u32>),
}

#[derive(Debug, Clone)]
pub struct AdtStructField {
    pub span: Span,
    pub idx: u32,
    pub vis: Visibility,
    pub ident: Option<Ident>,
    pub ty: LateInit<SpannedTy>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct AdtInstance {
    pub def: Obj<AdtDef>,
    pub params: TyOrReList,
}

// === Traits === //

#[derive(Debug, Clone)]
pub struct TraitDef {
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
    pub owner: Obj<TraitDef>,
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
pub struct ImplDef {
    pub item: Obj<Item>,
    pub generics: Obj<GenericBinder>,
    pub trait_: Option<SpannedTraitInstance>,
    pub target: SpannedTy,
    pub methods: LateInit<Vec<Obj<FnDef>>>,

    // We can't simply solve for stuff like `u32: Id<{T}>` where `{T}` is still unknown because
    // these impls could conflict...
    //
    // ```rust
    // pub trait Id<T> {}
    //
    // impl<T> Id<T> for T {}
    //
    // impl Id<i32> for u32 {}
    // ```
    //
    // Is `T` a `u32` or an `i32`? The other direction of `{T}: Id<i32>` is also problematic for the
    // same exact reason.
    //
    // To avoid potential combinatorial explosion from having to try out each candidate to figure
    // out which leads to a valid solution, we'll establish the following rule: if a trait
    // resolution is ever ambiguous, the entire resolution fails, regardless of whether backtrack
    // could reveal a solution.
    //
    // This gives as another useful rule: non-top-level trait solving should only ever be invoked if
    // the entire type is known.
    //
    // This gives us a solving algorithm:
    //
    // - Start by equating candidate type to `impl` target type.
    // - Repeatedly do constraint checking on the constraints whose clause parameter types and
    //   source types contain no remaining free inference variables.
    //
    // We can make this solving algorithm always work by ensuring that such a solving order exists
    // ahead of time as part of our well-formedness checks on `impl`s. I think this WF check is
    // equivalent to Rust's whole generic covered in `impl` rule.
    //
    // Anyways, this field encodes the solving order we found as part of our WF checks.
    pub generic_solve_order: LateInit<Vec<GenericSolveStep>>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct GenericSolveStep {
    pub generic_idx: u32,
    pub clause_idx: u32,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct TraitSpec {
    pub def: Obj<TraitDef>,
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
    pub def: Obj<TraitDef>,
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
    pub fn binder(self, s: &Session) -> Option<PosInBinder> {
        match self {
            AnyGeneric::Re(re) => *re.r(s).binder,
            AnyGeneric::Ty(ty) => *ty.r(s).binder,
        }
    }

    pub fn clauses(self, s: &Session) -> SpannedTraitClauseList {
        match self {
            AnyGeneric::Re(re) => *re.r(s).clauses,
            AnyGeneric::Ty(ty) => *ty.r(s).user_clauses,
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
    pub binder: LateInit<Option<PosInBinder>>,

    pub clauses: LateInit<SpannedTraitClauseList>,

    pub is_synthetic: bool,
}

#[derive_where(Debug)]
#[derive(Clone)]
pub struct TypeGeneric {
    #[derive_where(skip)]
    pub span: Span,

    pub ident: Ident,

    #[derive_where(skip)]
    pub binder: LateInit<Option<PosInBinder>>,

    /// The user-specified clauses on a generic type.
    pub user_clauses: LateInit<SpannedTraitClauseList>,

    /// All knowable facts about which traits the generic parameter implements.
    ///
    /// Unlike `user_clauses`, `elaborated_clauses` ensures that all generic parameters
    /// supplied to each trait clause will be of the form [`TraitParam::Equals`] and that all
    /// implicit bounds (including super-trait bounds) will be written out.
    ///
    /// The first element of the `elaborated_clauses` will always be an outlives constraint and
    /// there will always be exactly one such clause.
    #[derive_where(skip)]
    pub elaborated_clauses: LateInit<SpannedTraitClauseList>,

    /// Whether this generic was implicitly created rather than defined explicitly by the user.
    pub is_synthetic: bool,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct PosInBinder {
    pub def: Obj<GenericBinder>,
    pub idx: u32,
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

    /// Refers to a generic lifetime parameter.
    Universal(Obj<RegionGeneric>),

    /// An internal lifetime parameter within the body.
    InferVar(InferReVar),

    /// An explicit request to infer the lifetime.
    ExplicitInfer,

    /// The lifetime used when we don't want to worry about lifetimes.
    Erased,

    Error(ErrorGuaranteed),
}

pub type Ty = Intern<TyKind>;
pub type TyList = Intern<[Ty]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TyKind {
    /// The `Self`-type. This is expected to be substituted away before most analyses.
    This,

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
    FnDef(Obj<FnDef>),

    /// A user's explicit request to infer a type (i.e. `_`)
    ExplicitInfer,

    /// The universal type quantification produced by a generic parameter.
    Universal(Obj<TypeGeneric>),

    /// An inference variable used in trait solving. The second parameter is used in diagnostics to
    /// indicate the generic that led to the generation of this variable.
    InferVar(InferTyVar),

    Error(ErrorGuaranteed),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct InferReVar(pub u32);

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct InferTyVar(pub u32);

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
    TraitImpl(Obj<TraitDef>),

    /// A top-level coherence type indicating the implementation of a specific method in an inherent
    /// `impl` block. This type has exactly one child type indicating the implementation target.
    InherentMethodImpl(Symbol),

    Simple(SimpleTyKind),
    Re(Mutability),
    Adt(Obj<AdtDef>),
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
