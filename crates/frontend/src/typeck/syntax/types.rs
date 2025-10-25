use crate::{
    base::{
        arena::{Intern, LateInit, Obj},
        syntax::Span,
    },
    parse::token::Ident,
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
    pub span: Span,
    pub ident: Ident,
    pub generics: Obj<GenericBinder>,
    pub methods: LateInit<Vec<()>>,
    pub impls: LateInit<Vec<Obj<ImplDef>>>,
}

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
    pub trait_: Option<TraitSpec>,
    pub target: Ty,
    pub methods: LateInit<Vec<()>>,
}

#[derive(Debug, Clone)]
pub struct TraitSpec {
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
pub struct BinderSpec {
    pub def: Obj<GenericBinder>,
    pub idx: u32,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct GenericInstance {
    pub binder: Obj<GenericBinder>,
    pub substs: TyOrReList,
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
    pub ident: Ident,
    pub binder: LateInit<BinderSpec>,
    pub clauses: TraitClauseList,
}

#[derive(Debug, Clone)]
pub struct TypeGeneric {
    pub span: Span,
    pub ident: Ident,
    pub binder: LateInit<BinderSpec>,

    /// All knowable facts about which traits the generic parameter implements.
    pub uninstantiated_clauses: TraitClauseList,

    /// All knowable facts about which traits the generic parameter implements.
    ///
    /// Unlike `uninstantiated_clauses`, `instantiated_clauses` ensures that all generic parameters
    /// supplied to each trait clause will be of the form [`TraitParam::Equals`].
    pub instantiated_clauses: LateInit<TraitClauseList>,

    /// Whether this generic was implicitly created rather than defined explicitly by the user.
    pub is_synthetic: bool,
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
    Trait(Obj<TraitDef>, TraitClauseList),

    /// A tuple.
    Tuple(TyList),

    /// A statically-known function type. This can be coerced into a functional interface.
    FnDef(),

    /// A user's explicit request to infer a type (i.e. `_`)
    ExplicitInfer,

    /// The universal type quantification produced by a generic parameter.
    Universal(Obj<TypeGeneric>),

    /// An inference variable in the source of a type assignability check. Used for inference of
    /// types within a function body.
    SrcInferVar(InferTy),

    /// An inference variable in the destination of a type assignability check. Used for inference
    /// of types in a trait implementation candidate.
    DstInferVar(InferTy, TraitClauseList),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct InferTy(u32);

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
