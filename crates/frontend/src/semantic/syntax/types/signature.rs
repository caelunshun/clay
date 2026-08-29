use crate::{
    base::{
        ErrorGuaranteed, Session,
        arena::Obj,
        syntax::{Span, Symbol},
    },
    semantic::syntax::{
        AdtItem, HrtbDebruijn, Mutability, RegionGeneric, RelationDirection, SimpleTyKind,
        TraitItem, TyOrReKind, TypeAliasItem, TypeGeneric,
    },
};
use std::fmt;

// === Type === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigGenericList {
    pub segment_span: Span,
    pub elems: SigTyOrReList,
}

pub type SigTyOrReList = Obj<[SigTyOrRe]>;

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub enum SigTyOrRe {
    Re(SigRe),
    Ty(SigTy),
}

impl fmt::Debug for SigTyOrRe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SigTyOrRe::Re(re) => re.fmt(f),
            SigTyOrRe::Ty(ty) => ty.fmt(f),
        }
    }
}

impl SigTyOrRe {
    pub fn span(self, s: &Session) -> Span {
        match self {
            SigTyOrRe::Re(re) => re.span,
            SigTyOrRe::Ty(ty) => ty.r(s).span,
        }
    }
}

impl SigTyOrRe {
    pub fn kind(self) -> TyOrReKind {
        match self {
            SigTyOrRe::Re(_) => TyOrReKind::Re,
            SigTyOrRe::Ty(_) => TyOrReKind::Ty,
        }
    }

    pub fn as_re(self) -> Option<SigRe> {
        match self {
            SigTyOrRe::Re(v) => Some(v),
            SigTyOrRe::Ty(_) => None,
        }
    }

    pub fn as_ty(self) -> Option<SigTy> {
        match self {
            SigTyOrRe::Ty(v) => Some(v),
            SigTyOrRe::Re(_) => None,
        }
    }

    pub fn unwrap_re(self) -> SigRe {
        self.as_re().unwrap()
    }

    pub fn unwrap_ty(self) -> SigTy {
        self.as_ty().unwrap()
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigRe {
    pub span: Span,
    pub kind: SigReKind,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum SigReKind {
    /// The top region type. Essentially, this pointer is either managed by the garbage collector or
    /// lives for the entire duration of the program.
    Gc,

    /// A higher-ranked region variable within an HRTB binder (e.g. the `'a` in the type `Foo<'a>`
    /// in the clause `for<'a> Foo<'a>`).
    HrtbVar(HrtbDebruijn),

    /// An internal lifetime parameter within the body.
    Infer,

    /// An instantiated generic lifetime parameter.
    Generic(Obj<RegionGeneric>),

    Error(ErrorGuaranteed),
}

impl SigReKind {
    pub fn wrap(self, span: Span) -> SigRe {
        SigRe { span, kind: self }
    }
}

pub type SigTy = Obj<SigTyInner>;
pub type SigTyList = Obj<[SigTy]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigTyInner {
    pub span: Span,
    pub kind: SigTyKind,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum SigTyKind {
    /// The `Self` type.
    SelfTy,

    /// A reference to a type-generic.
    Generic(Obj<TypeGeneric>),

    /// A request to create an inference variable (e.g. `_`).
    Infer,

    /// A request to expand a type alias.
    Alias(Obj<TypeAliasItem>, SigGenericList),

    /// A request to expand a projection of a trait.
    Project(SigProjectType),

    /// A simple primitive non-composite type living for `'gc`.
    Simple(SimpleTyKind),

    /// A reference type.
    Reference(SigRe, Mutability, SigTy),

    /// An instantiation of an ADT.
    Adt(SigAdtInstance),

    /// A `&'re dyn Trait` object.
    Trait(SigRe, Mutability, SigTraitClauseList),

    /// A tuple.
    Tuple(SigTyList),

    /// A higher-ranked type variable within an HRTB binder (e.g. the `T` in the type `Foo<T>` in
    /// the clause `for<T> Foo<T>`).
    HrtbVar(HrtbDebruijn),

    Error(ErrorGuaranteed),
}

impl SigTyKind {
    pub fn wrap(self, span: Span, s: &Session) -> SigTy {
        Obj::new(SigTyInner { span, kind: self }, s)
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigAdtInstance {
    pub def: Obj<AdtItem>,
    pub params: SigGenericList,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigProjectType {
    pub target: SigTy,
    pub spec: SigTraitSpec,
    pub assoc_span: Span,
    pub assoc_idx: u32,
}

// === Trait === //

/// A trait clause with multiple parts (e.g. `'a + Foo<u32> + Bar<Item = Baz>`).
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigTraitClauseList {
    pub span: Span,
    pub elems: Obj<[SigTraitClause]>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigTraitClause {
    pub span: Span,
    pub kind: SigTraitClauseKind,
}

/// A single trait clause (e.g. `'a` or `Trait<'re1, Ty1, Ty2, AssocA = Ty3, AssocC = Ty4>`).
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum SigTraitClauseKind {
    Outlives(RelationDirection, SigTyOrRe),
    Trait(SigHrtbBinder),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigHrtbBinder {
    pub defs_span: Span,
    pub defs: SigHrtbDebruijnDefList,
    pub inner: SigTraitSpec,
}

pub type SigHrtbDebruijnDefList = Obj<[SigHrtbDebruijnDef]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigHrtbDebruijnDef {
    pub span: Span,
    pub name: Symbol,
    pub kind: TyOrReKind,
    pub clauses: SigTraitClauseList,
}

pub type SigTraitParamList = Obj<[SigTraitParam]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigTraitParam {
    pub span: Span,
    pub kind: SigTraitParamKind,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum SigTraitParamKind {
    Equals(SigTyOrRe),
    Unspecified(SigTraitClauseList),
}

impl SigTraitParamKind {
    pub fn wrap(self, span: Span) -> SigTraitParam {
        SigTraitParam { span, kind: self }
    }
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigTraitSpec {
    pub span: Span,
    pub def: Obj<TraitItem>,
    pub params: SigTraitParamList,
}

impl fmt::Debug for SigTraitSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &Session::fetch();

        f.debug_struct("TraitSpec")
            .field("def", &self.def.r(s).item.r(s).name.unwrap().text)
            .field("params", &self.params)
            .finish()
    }
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct SigTraitInstance {
    pub span: Span,
    pub def: Obj<TraitItem>,
    pub params: SigGenericList,
}

impl fmt::Debug for SigTraitInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &Session::fetch();

        f.debug_struct("TraitInstance")
            .field("def", &self.def.r(s).item.r(s).name.unwrap().text)
            .field("params", &self.params)
            .finish()
    }
}
