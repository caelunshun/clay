use crate::{
    base::{
        arena::{Intern, LateInit, Obj},
        syntax::{Span, Symbol},
    },
    parse::token::{Ident, Lifetime},
    typeck::syntax::{Func, Item},
    utils::hash::FxHashMap,
};

// === AdtDef === //

#[derive(Debug, Clone)]
pub struct AdtDef {
    pub span: Span,
    pub ident: Ident,
    pub generics: Obj<GenericBinder>,
    pub fields: Vec<AdtField>,
}

#[derive(Debug, Clone)]
pub struct AdtField {
    pub def: LateInit<Obj<AdtDef>>,
    pub idx: u32,
    pub ident: Span,
    pub ty: Ty,
}

// === Traits === //

#[derive(Debug, Clone)]
pub struct TraitDef {
    /// The item defining this trait.
    pub item: Obj<Item>,

    /// The set of parameter generics and associated types defined by this trait. This list starts
    /// with a `regular_generic_count` number of generic parameters followed by associated types.
    pub generics: LateInit<Obj<GenericBinder>>,

    /// The number of generic parameters taken by this trait.
    pub regular_generic_count: u32,

    /// Maps associated type names to the index of that parameters in the combined `generics`
    /// binder.
    pub associated_type_to_index: FxHashMap<Symbol, AssocType>,

    /// The set of methods defined by this trait.
    pub methods: LateInit<Vec<()>>,

    /// All known implementations of this trait.
    pub impls: LateInit<Vec<Obj<ImplDef>>>,
}

#[derive(Debug, Copy, Clone)]
pub struct AssocType {
    pub span: Span,
    pub idx: u32,
}

pub type ListOfTraitClauseList = Intern<[TraitClauseList]>;

/// A trait clause with multiple parts (e.g. `'a + Foo<u32> + Bar<Item = Baz>`).
pub type TraitClauseList = Intern<[TraitClause]>;

/// A single trait clause (e.g. `'a` or `Trait<'re1, Ty1, Ty2, AssocA = Ty3, AssocC = Ty4>`).
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TraitClause {
    Outlives(Re),
    Trait(Obj<TraitDef>, TraitParamList),
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
    pub span: Span,
    pub generics: Obj<GenericBinder>,
    pub trait_: Option<TraitInstance>,
    pub target: Ty,
    pub methods: LateInit<Vec<()>>,

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

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct TraitInstance {
    pub def: Obj<TraitDef>,
    pub params: TyOrReList,
}

// === Generics === //

/// A container for a list of generics which can be substituted all at once.
#[derive(Debug, Clone)]
pub struct GenericBinder {
    pub span: Span,
    pub generics: Vec<AnyGeneric>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AnyGeneric {
    Re(Obj<RegionGeneric>),
    Ty(Obj<TypeGeneric>),
}

impl AnyGeneric {
    pub fn unwrap_re(self) -> Obj<RegionGeneric> {
        let Self::Re(v) = self else {
            unreachable!();
        };

        v
    }

    pub fn unwrap_ty(self) -> Obj<TypeGeneric> {
        let Self::Ty(v) = self else {
            unreachable!();
        };

        v
    }
}

#[derive(Debug, Clone)]
pub struct RegionGeneric {
    pub span: Span,
    pub lifetime: Lifetime,
    pub binder: LateInit<PosInBinder>,
    pub clauses: TraitClauseList,
}

#[derive(Debug, Clone)]
pub struct TypeGeneric {
    pub span: Span,
    pub ident: Ident,
    pub binder: LateInit<PosInBinder>,

    /// The user-specified clauses on a generic type.
    pub user_clauses: TraitClauseList,

    /// All knowable facts about which traits the generic parameter implements.
    ///
    /// Unlike `user_clauses`, `instantiated_clauses` ensures that all generic parameters
    /// supplied to each trait clause will be of the form [`TraitParam::Equals`] and that all
    /// implicit bounds (including super-trait bounds) will be written out.
    pub instantiated_clauses: LateInit<TraitClauseList>,

    /// Whether this generic was implicitly created rather than defined explicitly by the user.
    pub is_synthetic: bool,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct PosInBinder {
    pub def: Obj<GenericBinder>,
    pub idx: u32,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct GenericInstance {
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
    pub fn unwrap_re(self) -> Re {
        let Self::Re(v) = self else {
            unreachable!();
        };

        v
    }

    pub fn unwrap_ty(self) -> Ty {
        let Self::Ty(v) = self else {
            unreachable!();
        };

        v
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum Re {
    /// The top region type. Essentially, this pointer is either managed by the garbage collector or
    /// lives for the entire duration of the program.
    Gc,

    /// Refers to a generic lifetime parameter.
    Generic(Obj<RegionGeneric>),

    /// An internal lifetime parameter within the body.
    InferVar(i32),

    /// An explicit request to infer the lifetime.
    ExplicitInfer,

    /// The lifetime used when we don't want to worry about lifetimes.
    Erased,
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
    Reference(Re, Ty),

    /// An instantiation of an ADT.
    Adt(Obj<AdtDef>, TyOrReList),

    /// A `dyn Trait` object.
    Trait(TraitClauseList),

    /// A tuple.
    Tuple(TyList),

    /// A statically-known function type. This can be coerced into a functional interface.
    FnDef(Obj<Func>),

    /// A user's explicit request to infer a type (i.e. `_`)
    ExplicitInfer,

    /// The universal type quantification produced by a generic parameter.
    Universal(Obj<TypeGeneric>),

    /// An inference variable used in trait solving. The second parameter is used in diagnostics to
    /// indicate the generic that led to the generation of this variable.
    InferVar(InferTyVar, Obj<TypeGeneric>),
}

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

// === Variance === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum Variance {
    Invariant,
    Covariant,
    Contravariant,
}

impl Variance {
    pub fn rev(self) -> Self {
        match self {
            Variance::Invariant => Variance::Invariant,
            Variance::Covariant => Variance::Contravariant,
            Variance::Contravariant => Variance::Covariant,
        }
    }
}
