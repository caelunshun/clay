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
    pub methods: Vec<()>,
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
    Implements(TraitClauseList),

    /// The constraints for this generic parameter have been omitted. This is only valid if the
    Unspecified,
}

// === Generics === //

/// A definition site for multiple generics.
#[derive(Debug, Clone)]
pub struct GenericBinder {
    pub span: Span,
    pub generics: Vec<AnyGeneric>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct GenericInstance {
    pub binder: Obj<GenericBinder>,
    pub substs: TyOrReList,
}

/// A definition for any type of generic.
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

/// A definition for a generic region parameter.
#[derive(Debug, Clone)]
pub struct RegionGeneric {
    pub span: Span,
    pub ident: Ident,
    pub binder: LateInit<Obj<GenericBinder>>,
    pub index_in_binder: u32,
    pub clause: TraitClauseList,
    pub variance: Variance,
}

/// A definition for a generic type parameter.
#[derive(Debug, Clone)]
pub struct TypeGeneric {
    pub span: Span,
    pub ident: Ident,
    pub binder: LateInit<Obj<GenericBinder>>,
    pub index_in_binder: u32,
    pub unspecified_clause: TraitClauseList,
    pub fully_specified_clause: LateInit<TraitClauseList>,
    pub is_synthetic: bool,
    pub is_associated_type: bool,
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
    Internal(i32),

    /// An explicit request to infer the lifetime.
    Infer,

    /// The lifetime used when we don't want to worry about lifetimes.
    Erased,
}

pub type Ty = Intern<TyKind>;
pub type TyList = Intern<[Ty]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TyKind {
    This,
    Simple(SimpleTyKind),
    RawSlice(Ty),
    Adt(Obj<AdtDef>, TyOrReList),
    Trait(Obj<TraitDef>, TyOrReList),
    Tuple(TyList),
    FnDef(),
    Reference(Re, Ty),
    Generic(Obj<TypeGeneric>),
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
