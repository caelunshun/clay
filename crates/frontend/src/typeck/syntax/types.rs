use crate::{
    base::{
        Session,
        arena::{LateInit, Obj},
    },
    parse::token::Ident,
};

// === Trait Definitions === //

#[derive(Debug, Clone)]
pub struct TraitDef {
    pub name: Ident,
    pub generics: Vec<AnyGeneric>,
    pub methods: Vec<Obj<TraitMethod>>,
    pub super_type: Ty,
}

#[derive(Debug, Clone)]
pub struct TraitMethod {
    pub name: Ident,
    pub trait_: LateInit<Obj<TraitDef>>,
    pub generics: Vec<AnyGeneric>,
    pub args: TyList,
    pub arg_names: Vec<Ident>,
    pub ret_ty: Ty,
}

// === ADT Definition === //

#[derive(Debug, Clone)]
pub struct AdtDef {
    pub name: Ident,
    pub generics: Vec<AnyGeneric>,
    pub kind: AdtKind,
    pub fields: Vec<Obj<AdtField>>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AdtKind {
    Enum,
    Struct,
}

#[derive(Debug, Clone)]
pub struct AdtField {
    pub def: LateInit<Obj<AdtDef>>,
    pub name: Ident,
    pub ty: Ty,
}

// === Generics === //

#[derive(Debug, Clone)]
pub struct GenericBinder {
    pub items: Vec<AnyGeneric>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct GenericInstance {
    pub binder: Obj<GenericBinder>,
    pub types: TyOrReList,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AnyGeneric {
    Type(Obj<GenericType>),
    Region(Obj<GenericRegion>),
}

#[derive(Debug, Clone)]
pub struct GenericType {
    pub binder: LateInit<Obj<GenericBinder>>,
    pub index: u32,
    pub name: Ident,
    pub inherits: Ty,
}

#[derive(Debug, Clone)]
pub struct GenericRegion {
    pub binder: LateInit<Obj<GenericBinder>>,
    pub index: u32,
    pub name: Ident,
    pub outlives: Re,
    pub variance: Variance,
}

// === Type === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct Ty {
    inner: Obj<TyKind>,
}

impl Ty {
    pub fn new_unchecked(inner: Obj<TyKind>) -> Self {
        Self { inner }
    }

    pub fn r(self, s: &Session) -> &TyKind {
        self.inner.r(s)
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct TyList {
    inner: Obj<[Ty]>,
}

impl TyList {
    pub fn new_unchecked(inner: Obj<[Ty]>) -> Self {
        Self { inner }
    }

    pub fn r(self, s: &Session) -> &[Ty] {
        self.inner.r(s)
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum TyKind {
    This,
    Simple(SimpleTyKind),
    RawSlice(Ty),
    Adt(Obj<AdtDef>, TyOrReList),
    Trait(Obj<TraitDef>, TyOrReList),
    Tuple(TyList),
    FnDef(),
    Reference(Re, Ty),
    Generic(Obj<GenericType>),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum Re {
    /// The top region type. Essentially, this pointer is either managed by the garbage collector or
    /// lives for the entire duration of the program.
    Gc,

    /// Refers to a generic lifetime parameter.
    Generic(Obj<GenericRegion>),

    /// An internal lifetime parameter within the body.
    Internal(i32),

    /// An explicit request to infer the lifetime.
    Infer,

    /// The lifetime used when we don't want to worry about lifetimes.
    Erased,
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

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TyOrRe {
    Ty(Ty),
    Re(Re),
}

impl TyOrRe {
    pub fn unwrap_ty(self) -> Ty {
        let Self::Ty(v) = self else {
            unreachable!();
        };

        v
    }

    pub fn unwrap_re(self) -> Re {
        let Self::Re(v) = self else {
            unreachable!();
        };

        v
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct TyOrReList {
    inner: Obj<[TyOrRe]>,
}

impl TyOrReList {
    pub fn new_unchecked(inner: Obj<[TyOrRe]>) -> Self {
        Self { inner }
    }

    pub fn r(self, s: &Session) -> &[TyOrRe] {
        self.inner.r(s)
    }
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
