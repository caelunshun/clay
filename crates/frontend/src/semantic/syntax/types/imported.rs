use crate::{
    base::{
        ErrorGuaranteed, Session,
        arena::{HasInterner, HasListInterner, Intern, LateInit, Obj},
        syntax::{Span, Symbol},
    },
    semantic::syntax::{
        AdtCtor, AdtItem, AnyGeneric, FloatKind, FnDef, FnItem, GenericBinder, HrtbDebruijn,
        ImplItem, IntKind, LocalNameIdent, MirLocalIdx, Mutability, RegionGeneric,
        RelationDirection, SimpleTyKind, TraitItem, TyCtxt, TyOrReKind, TypeGeneric,
    },
    symbol,
};
use index_vec::define_index_type;
use std::{fmt, rc::Rc};

// === Type === //

pub type TyOrReList = Intern<[TyOrRe]>;

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub enum TyOrRe {
    Re(Re),
    Ty(Ty),
}

impl fmt::Debug for TyOrRe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyOrRe::Re(re) => re.fmt(f),
            TyOrRe::Ty(ty) => ty.fmt(f),
        }
    }
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

    /// An generic region variable within an HRTB binder (e.g. the `'a` in the type
    /// `Foo<'a>` in the clause `for<'a> Foo<'a>`).
    ///
    /// These regions always show up under a binder. To liberate a binder, these regions are
    /// instantiated into a `UniversalVar` or an `InferVar` during trait obligation checking
    /// depending on how the HRTB is being used.
    ///
    /// These are indexed using debruijn indices.
    HrtbVar(HrtbDebruijn),

    /// An internal lifetime parameter within the body.
    InferVar(InferReVar),

    /// A universally-quantified lifetime parameter.
    UniversalVar(UniversalReVar),

    /// The lifetime used when we don't want to worry about lifetimes.
    Erased,

    Error(ErrorGuaranteed),
}

pub type Ty = Intern<TyKind>;
pub type TyList = Intern<[Ty]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TyKind {
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

    /// An generic type variable within an HRTB binder (e.g. the `T` in the type
    /// `Foo<T>` in the clause `for<T> Foo<T>`).
    ///
    /// These types always show up under a binder. To liberate a binder, these types are
    /// instantiated into a `UniversalVar` or an `InferVar` during trait obligation checking
    /// depending on how the HRTB is being used.
    ///
    /// These are indexed using debruijn indices.
    HrtbVar(HrtbDebruijn),

    /// An inference variable.
    InferVar(InferTyVar),

    /// An universal type variable.
    UniversalVar(UniversalTyVar),

    Error(ErrorGuaranteed),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct AdtInstance {
    pub def: Obj<AdtItem>,
    pub params: TyOrReList,
}

// === Trait === //

pub type ListOfTraitClauseList = Intern<[TraitClauseList]>;

/// A trait clause with multiple parts (e.g. `'a + Foo<u32> + Bar<Item = Baz>`).
pub type TraitClauseList = Intern<[TraitClause]>;

/// A single trait clause (e.g. `'a` or `Trait<'re1, Ty1, Ty2, AssocA = Ty3, AssocC = Ty4>`).
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TraitClause {
    Outlives(RelationDirection, TyOrRe),
    Trait(HrtbBinder),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct HrtbBinder {
    pub defs: HrtbDebruijnDefList,
    pub inner: TraitSpec,
}

pub type HrtbDebruijnDefList = Intern<[HrtbDebruijnDef]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct HrtbDebruijnDef {
    pub span: Span,
    pub name: Symbol,
    pub kind: TyOrReKind,
    pub clauses: TraitClauseList,
}

pub type TraitParamList = Intern<[TraitParam]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TraitParam {
    Equals(TyOrRe),
    Unspecified(TraitClauseList),
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

impl TraitInstance {
    pub fn to_spec(self, tcx: &TyCtxt) -> TraitSpec {
        let s = &tcx.session;

        TraitSpec {
            def: self.def,
            params: tcx.intern_list(
                &self
                    .params
                    .r(s)
                    .iter()
                    .map(|&para| TraitParam::Equals(para))
                    .collect::<Vec<_>>(),
            ),
        }
    }
}

// === FnInstance === //

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
    Trait(FnOwnerTrait),
    Inherent(FnOwnerInherent),
    AdtCtor(FnOwnerAdtCtor),
}

impl FnOwner {
    pub fn early_generics(self, s: &Session) -> Obj<GenericBinder> {
        match self {
            FnOwner::Item(owner) => owner.early_generics(s),
            FnOwner::Trait(owner) => owner.early_generics(s),
            FnOwner::Inherent(owner) => owner.early_generics(s),
            FnOwner::AdtCtor(owner) => owner.early_generics(s),
        }
    }

    pub fn has_self_parameter(self, s: &Session) -> bool {
        match self {
            FnOwner::Item(owner) => owner.has_self_parameter(s),
            FnOwner::Trait(owner) => owner.has_self_parameter(s),
            FnOwner::Inherent(owner) => owner.has_self_parameter(s),
            FnOwner::AdtCtor(owner) => owner.has_self_parameter(s),
        }
    }

    pub fn unimported_sig_args(self, tcx: &TyCtxt) -> TyList {
        match self {
            FnOwner::Item(owner) => owner.unimported_sig_args(tcx),
            FnOwner::Trait(owner) => owner.unimported_sig_args(tcx),
            FnOwner::Inherent(owner) => owner.unimported_sig_args(tcx),
            FnOwner::AdtCtor(owner) => owner.unimported_sig_args(tcx),
        }
    }

    pub fn unimported_sig_ret_ty(self, tcx: &TyCtxt) -> Ty {
        match self {
            FnOwner::Item(owner) => owner.unimported_sig_ret_ty(tcx),
            FnOwner::Trait(owner) => owner.unimported_sig_ret_ty(tcx),
            FnOwner::Inherent(owner) => owner.unimported_sig_ret_ty(tcx),
            FnOwner::AdtCtor(owner) => owner.unimported_sig_ret_ty(tcx),
        }
    }
}

pub trait FnOwnerBackedByDef: Copy {
    fn def(self, s: &Session) -> Obj<FnDef>;

    fn early_generics(self, s: &Session) -> Obj<GenericBinder> {
        self.def(s).r(s).generics
    }

    fn has_self_parameter(self, s: &Session) -> bool {
        *self.def(s).r(s).has_self_param
    }

    fn unimported_sig_args(self, tcx: &TyCtxt) -> TyList {
        let s = &tcx.session;

        tcx.intern_list(
            &self
                .def(s)
                .r(s)
                .args
                .r(s)
                .iter()
                .map(|arg| arg.ty.value)
                .collect::<Vec<_>>(),
        )
    }

    fn unimported_sig_ret_ty(self, tcx: &TyCtxt) -> Ty {
        let s = &tcx.session;

        self.def(s).r(s).ret_ty.value
    }
}

impl FnOwnerBackedByDef for Obj<FnItem> {
    fn def(self, s: &Session) -> Obj<FnDef> {
        *self.r(s).def
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct FnOwnerTrait {
    pub instance: TraitSpec,
    pub self_ty: Ty,
    pub method_idx: u32,
}

impl FnOwnerBackedByDef for FnOwnerTrait {
    fn def(self, s: &Session) -> Obj<FnDef> {
        self.instance.def.r(s).methods[self.method_idx as usize]
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct FnOwnerInherent {
    pub self_ty: Ty,
    pub block: Obj<ImplItem>,
    pub method_idx: u32,
}

impl FnOwnerBackedByDef for FnOwnerInherent {
    fn def(self, s: &Session) -> Obj<FnDef> {
        self.block.r(s).methods[self.method_idx as usize].unwrap()
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct FnOwnerAdtCtor {
    pub ctor: Obj<AdtCtor>,
}

impl FnOwnerAdtCtor {
    pub fn early_generics(self, s: &Session) -> Obj<GenericBinder> {
        self.ctor.r(s).owner.item(s).r(s).generics
    }

    pub fn has_self_parameter(self, _s: &Session) -> bool {
        false
    }

    pub fn unimported_sig_args(self, tcx: &TyCtxt) -> TyList {
        let s = &tcx.session;

        assert!(self.ctor.r(s).syntax.is_tuple());

        tcx.intern_list(
            &self
                .ctor
                .r(s)
                .fields
                .iter()
                .map(|field| field.ty.value)
                .collect::<Vec<_>>(),
        )
    }

    pub fn unimported_sig_ret_ty(self, tcx: &TyCtxt) -> Ty {
        let s = &tcx.session;
        let def = self.ctor.r(s).owner.item(s);

        tcx.intern(TyKind::Adt(AdtInstance {
            def: def,
            params: tcx.intern_list(
                &def.r(s)
                    .generics
                    .r(s)
                    .defs
                    .iter()
                    .map(|&para| match para {
                        AnyGeneric::Re(generic) => TyOrRe::Re(Re::SigGeneric(generic)),
                        AnyGeneric::Ty(generic) => {
                            TyOrRe::Ty(tcx.intern(TyKind::SigGeneric(generic)))
                        }
                    })
                    .collect::<Vec<_>>(),
            ),
        }))
    }
}

// === Universal Var === //

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
    HrtbVar,
    MirLocal(MirLocalIdx),
}

#[derive(Debug, Copy, Clone)]
pub enum UniversalTyVarSourceInfo {
    TraitSelf,
    HrtbVar,
    Root(Obj<TypeGeneric>),
    Projection(UniversalTyVar, TraitSpec, u32),
}

// === Infer Var === //

define_index_type! {
    pub struct InferReVar = u32;
}

define_index_type! {
    pub struct InferTyVar = u32;
}

#[derive(Debug, Clone)]
pub enum InferTyVarSourceInfo {
    UniversalElabHelper,
    TraitAssocPlaceholderHelper,
    HrtbLhsInstantiation {
        span: Span,
        clauses: Rc<LateInit<TraitClauseList>>,
    },
    ProjectionResult {
        span: Span,
    },
    Imported {
        span: Span,
    },
    Local {
        name: LocalNameIdent,
    },
    FunctionArgs {
        span: Span,
    },
    FunctionRetVal {
        span: Span,
    },
    MethodReceiver {
        span: Span,
    },
    OverloadedResult {
        span: Span,
    },
    Literal {
        span: Span,
    },
    ForLoopElem {
        span: Span,
    },
    IndexInput {
        span: Span,
    },
    IndexOutput {
        span: Span,
    },
    LoopDemand {
        span: Span,
    },
    HoleInfer {
        span: Span,
    },
    PatType {
        span: Span,
    },
    EmptyArrayElem {
        span: Span,
    },
    UnifyHelper,
    DerefHelper,
    MethodLookupHelper,
}

bitflags::bitflags! {
    #[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
    pub struct SimpleTySet: u16 {
        // === Categories === //

        /// Types which could be a `UniversalVar`.
        const MAYBE_UNIVERSAL = Self::OTHER.bits() | Self::ELAB_UNIVERSAL_VAR.bits();

        const UNSIGNED_INT = Self::U8.bits() | Self::U16.bits() | Self::U32.bits() | Self::U64.bits();
        const SIGNED_INT = Self::I8.bits() | Self::I16.bits() | Self::I32.bits() | Self::I64.bits();
        const INT = Self::UNSIGNED_INT.bits() | Self::SIGNED_INT.bits();
        const FLOAT = Self::F32.bits() | Self::F64.bits();
        const NUM = Self::INT.bits() | Self::FLOAT.bits();
        const SIGNED_NUM = Self::SIGNED_INT.bits() | Self::FLOAT.bits();

        // === Variants === //

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

        // Not used for inference. We just reuse the `SimpleTySet` machinery to simplify
        // arithmetic checking.
        const BOOL = 1 << 11;
        const CHAR = 1 << 12;

        const ELAB_UNIVERSAL_VAR = 1 << 13;
    }
}

impl SimpleTySet {
    pub fn names(self) -> Vec<Symbol> {
        let mut names = Vec::new();
        let mut bits = self.bits();

        while bits != 0 {
            let curr = 1 << bits.trailing_zeros();
            bits ^= curr;

            match SimpleTySet::from_bits_retain(curr) {
                SimpleTySet::OTHER | SimpleTySet::ELAB_UNIVERSAL_VAR => {
                    // (ignored)
                }
                SimpleTySet::U8 => names.push(symbol!("u8")),
                SimpleTySet::U16 => names.push(symbol!("u16")),
                SimpleTySet::U32 => names.push(symbol!("u32")),
                SimpleTySet::U64 => names.push(symbol!("u64")),
                SimpleTySet::I8 => names.push(symbol!("i8")),
                SimpleTySet::I16 => names.push(symbol!("i16")),
                SimpleTySet::I32 => names.push(symbol!("i32")),
                SimpleTySet::I64 => names.push(symbol!("i64")),
                SimpleTySet::F32 => names.push(symbol!("f32")),
                SimpleTySet::F64 => names.push(symbol!("f64")),
                SimpleTySet::BOOL => names.push(symbol!("bool")),
                SimpleTySet::CHAR => names.push(symbol!("char")),

                v => unreachable!("{v:?}"),
            }
        }

        names
    }

    pub fn can_accept_type(self, ty: Ty, s: &Session) -> bool {
        match *ty.r(s) {
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
            )
            | TyKind::Error(_) => self.contains(SimpleTySet::OTHER),

            TyKind::InferVar(_) => unreachable!(),
        }
    }

    pub fn to_unique_type(self, tcx: &TyCtxt) -> Option<Ty> {
        if self.bits().count_ones() != 1 {
            return None;
        }

        let kind = match SimpleTySet::from_bits_retain(1 << self.bits().trailing_zeros()) {
            SimpleTySet::OTHER | SimpleTySet::ELAB_UNIVERSAL_VAR => None,
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
            SimpleTySet::BOOL => Some(SimpleTyKind::Bool),
            SimpleTySet::CHAR => Some(SimpleTyKind::Char),

            v => unreachable!("{v:?}"),
        }?;

        Some(tcx.intern(TyKind::Simple(kind)))
    }

    pub fn to_infer_fallback(self, tcx: &TyCtxt) -> Option<Ty> {
        if self.intersects(SimpleTySet::I32) {
            return Some(tcx.intern(TyKind::Simple(SimpleTyKind::Int(IntKind::S32))));
        }

        if self.intersects(SimpleTySet::I64) {
            return Some(tcx.intern(TyKind::Simple(SimpleTyKind::Int(IntKind::S64))));
        }

        if self.intersects(SimpleTySet::U32) {
            return Some(tcx.intern(TyKind::Simple(SimpleTyKind::Uint(IntKind::S32))));
        }

        if self.intersects(SimpleTySet::U64) {
            return Some(tcx.intern(TyKind::Simple(SimpleTyKind::Uint(IntKind::S64))));
        }

        if self.intersects(SimpleTySet::F32) {
            return Some(tcx.intern(TyKind::Simple(SimpleTyKind::Float(FloatKind::S32))));
        }

        if self.intersects(SimpleTySet::F64) {
            return Some(tcx.intern(TyKind::Simple(SimpleTyKind::Float(FloatKind::S64))));
        }

        None
    }
}
