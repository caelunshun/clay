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
    pub generics: Obj<GenericDefs>,
    pub methods: Vec<Obj<TraitMethod>>,
    pub super_type: Ty,
}

#[derive(Debug, Clone)]
pub struct TraitMethod {
    pub name: Ident,
    pub parent: LateInit<Obj<TraitDef>>,
    pub generics: Obj<GenericDefs>,
    pub args: TyList,
    pub arg_names: Vec<Ident>,
    pub ret_ty: Ty,
}

// === ADT Definition === //

#[derive(Debug, Clone)]
pub struct AdtDef {
    pub name: Ident,
    pub generics: Obj<GenericDefs>,
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
pub struct GenericDefs {
    pub parent: Option<Obj<GenericDefs>>,
    pub params: Vec<AnyGeneric>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AnyGeneric {
    Type(Obj<GenericType>),
    Region(Obj<GenericRegion>),
}

#[derive(Debug, Clone)]
pub struct GenericType {
    pub defs: LateInit<Obj<GenericDefs>>,
    pub index: u32,
    pub name: Ident,
    pub inherits: Ty,
}

#[derive(Debug, Clone)]
pub struct GenericRegion {
    pub defs: LateInit<Obj<GenericDefs>>,
    pub index: u32,
    pub name: Ident,
    pub outlives: Re,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct Instance {
    inner: Obj<InstanceInner>,
}

impl Instance {
    pub fn new_unchecked(inner: Obj<InstanceInner>) -> Self {
        Self { inner }
    }

    pub fn r(self, s: &Session) -> &InstanceInner {
        self.inner.r(s)
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct InstanceInner {
    pub parent: Option<Instance>,
    pub def: Obj<GenericDefs>,
    pub values: TyList,
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
    Adt(Obj<AdtDef>, TyList),
    Trait(Obj<TraitDef>, TyList),
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
    Bool,
    Char,
    Int(IntKind),
    Uint(IntKind),
    Float(FloatKind),
    Str,
    Never,
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
