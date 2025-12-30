use crate::{
    base::{
        ErrorGuaranteed,
        analysis::{Spanned, SpannedInfo, SpannedViewDecode, SpannedViewEncode},
        arena::{HasInterner, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::TyCtxt,
        syntax::{
            AdtInstance, AdtItem, FnDef, InferTyVar, Mutability, Re, SimpleTyKind, TraitClause,
            TraitClauseList, TraitInstance, TraitItem, TraitParam, TraitParamList, TraitSpec, Ty,
            TyKind, TyList, TyOrRe, TyOrReList, TyProjection, TypeGeneric, UniversalTyVar,
        },
    },
};

// === Lists === //

pub type SpannedTyOrReList = Spanned<TyOrReList>;
pub type SpannedTyList = Spanned<TyList>;
pub type SpannedTraitClauseList = Spanned<TraitClauseList>;
pub type SpannedTraitParamList = Spanned<TraitParamList>;

// === TyOrRe === //

pub type SpannedTyOrRe = Spanned<TyOrRe>;

#[derive(Debug, Copy, Clone)]
pub enum SpannedTyOrReView {
    Re(SpannedRe),
    Ty(SpannedTy),
}

impl SpannedViewDecode<TyCtxt> for TyOrRe {
    type View = SpannedTyOrReView;

    fn decode(value: &Self, span_info: SpannedInfo, tcx: &TyCtxt) -> Self::View {
        match *value {
            TyOrRe::Re(re) => SpannedTyOrReView::Re(Spanned::new_raw(re, span_info.unwrap(tcx))),
            TyOrRe::Ty(ty) => SpannedTyOrReView::Ty(Spanned::new_raw(ty, span_info.unwrap(tcx))),
        }
    }
}

impl SpannedViewEncode<TyCtxt> for SpannedTyOrReView {
    type Unspanned = TyOrRe;

    fn encode(self, own_span: Span, tcx: &TyCtxt) -> Spanned<Self::Unspanned> {
        match self {
            SpannedTyOrReView::Re(re) => {
                Spanned::new_raw(TyOrRe::Re(re.value), re.span_info.wrap(own_span, tcx))
            }
            SpannedTyOrReView::Ty(ty) => {
                Spanned::new_raw(TyOrRe::Ty(ty.value), ty.span_info.wrap(own_span, tcx))
            }
        }
    }
}

// === Ty === //

pub type SpannedTy = Spanned<Ty>;

#[derive(Debug, Copy, Clone)]
pub enum SpannedTyView {
    SigThis,
    SigInfer,
    SigGeneric(Obj<TypeGeneric>),
    SigProject(SpannedTyProjection),
    Simple(SimpleTyKind),
    Reference(SpannedRe, Mutability, SpannedTy),
    Adt(SpannedAdtInstance),
    Trait(SpannedTraitClauseList),
    Tuple(SpannedTyList),
    FnDef(Obj<FnDef>, Option<SpannedTyOrReList>),
    InferVar(InferTyVar),
    UniversalVar(UniversalTyVar),
    Error(ErrorGuaranteed),
}

impl SpannedViewDecode<TyCtxt> for Ty {
    type View = SpannedTyView;

    fn decode(value: &Self, span_info: SpannedInfo, tcx: &TyCtxt) -> Self::View {
        let s = &tcx.session;

        match *value.r(s) {
            TyKind::SigThis => SpannedTyView::SigThis,
            TyKind::SigInfer => SpannedTyView::SigInfer,
            TyKind::SigGeneric(generic) => SpannedTyView::SigGeneric(generic),
            TyKind::SigProject(project) => {
                SpannedTyView::SigProject(Spanned::new_raw(project, span_info.unwrap(tcx)))
            }
            TyKind::Simple(kind) => SpannedTyView::Simple(kind),
            TyKind::Reference(re, muta, pointee) => {
                let [re_span, pointee_span] = span_info.child_spans(tcx);

                SpannedTyView::Reference(
                    Spanned::new_raw(re, re_span),
                    muta,
                    Spanned::new_raw(pointee, pointee_span),
                )
            }
            TyKind::Adt(adt) => SpannedTyView::Adt(Spanned::new_raw(adt, span_info.unwrap(tcx))),
            TyKind::Trait(clauses) => {
                SpannedTyView::Trait(Spanned::new_raw(clauses, span_info.unwrap(tcx)))
            }
            TyKind::Tuple(tys) => {
                SpannedTyView::Tuple(Spanned::new_raw(tys, span_info.unwrap(tcx)))
            }
            TyKind::FnDef(def, generics) => SpannedTyView::FnDef(
                def,
                generics.map(|generics| Spanned::new_raw(generics, span_info.unwrap(tcx))),
            ),
            TyKind::InferVar(var) => SpannedTyView::InferVar(var),
            TyKind::UniversalVar(var) => SpannedTyView::UniversalVar(var),
            TyKind::Error(error) => SpannedTyView::Error(error),
        }
    }
}

impl SpannedViewEncode<TyCtxt> for SpannedTyView {
    type Unspanned = Ty;

    fn encode(self, own_span: Span, tcx: &TyCtxt) -> Spanned<Self::Unspanned> {
        match self {
            SpannedTyView::SigThis => Spanned::new_raw(
                tcx.intern(TyKind::SigThis),
                SpannedInfo::new_terminal(own_span, tcx),
            ),
            SpannedTyView::SigInfer => Spanned::new_raw(
                tcx.intern(TyKind::SigInfer),
                SpannedInfo::new_terminal(own_span, tcx),
            ),
            SpannedTyView::SigGeneric(generic) => Spanned::new_raw(
                tcx.intern(TyKind::SigGeneric(generic)),
                SpannedInfo::new_terminal(own_span, tcx),
            ),
            SpannedTyView::SigProject(project) => Spanned::new_raw(
                tcx.intern(TyKind::SigProject(project.value)),
                project.span_info.wrap(own_span, tcx),
            ),
            SpannedTyView::Simple(kind) => Spanned::new_raw(
                tcx.intern(TyKind::Simple(kind)),
                SpannedInfo::new_terminal(own_span, tcx),
            ),
            SpannedTyView::Reference(re, muta, pointee) => Spanned::new_raw(
                tcx.intern(TyKind::Reference(re.value, muta, pointee.value)),
                SpannedInfo::new_list(own_span, &[re.span_info, pointee.span_info], tcx),
            ),
            SpannedTyView::Adt(adt) => Spanned::new_raw(
                tcx.intern(TyKind::Adt(adt.value)),
                adt.span_info.wrap(own_span, tcx),
            ),
            SpannedTyView::Trait(clauses) => Spanned::new_raw(
                tcx.intern(TyKind::Trait(clauses.value)),
                clauses.span_info.wrap(own_span, tcx),
            ),
            SpannedTyView::Tuple(tys) => Spanned::new_raw(
                tcx.intern(TyKind::Tuple(tys.value)),
                tys.span_info.wrap(own_span, tcx),
            ),
            SpannedTyView::FnDef(def, Some(generics)) => Spanned::new_raw(
                tcx.intern(TyKind::FnDef(def, Some(generics.value))),
                SpannedInfo::new_list(own_span, &[generics.span_info], tcx),
            ),
            SpannedTyView::FnDef(def, None) => Spanned::new_raw(
                tcx.intern(TyKind::FnDef(def, None)),
                SpannedInfo::new_terminal(own_span, tcx),
            ),
            SpannedTyView::InferVar(var) => Spanned::new_raw(
                tcx.intern(TyKind::InferVar(var)),
                SpannedInfo::new_terminal(own_span, tcx),
            ),
            SpannedTyView::UniversalVar(var) => Spanned::new_raw(
                tcx.intern(TyKind::UniversalVar(var)),
                SpannedInfo::new_terminal(own_span, tcx),
            ),
            SpannedTyView::Error(error_guaranteed) => Spanned::new_raw(
                tcx.intern(TyKind::Error(error_guaranteed)),
                SpannedInfo::new_terminal(own_span, tcx),
            ),
        }
    }
}

// === Region === //

pub type SpannedRe = Spanned<Re>;

impl SpannedViewDecode<TyCtxt> for Re {
    type View = Re;

    fn decode(value: &Self, _span_info: SpannedInfo, _tcx: &TyCtxt) -> Self::View {
        *value
    }
}

impl SpannedViewEncode<TyCtxt> for Re {
    type Unspanned = Re;

    fn encode(self, own_span: Span, tcx: &TyCtxt) -> Spanned<Self::Unspanned> {
        Spanned::new_raw(self, SpannedInfo::new_terminal(own_span, tcx))
    }
}

// === TraitClause === //

pub type SpannedTraitClause = Spanned<TraitClause>;

#[derive(Debug, Copy, Clone)]
pub enum SpannedTraitClauseView {
    Outlives(SpannedRe),
    Trait(SpannedTraitSpec),
}

impl SpannedViewDecode<TyCtxt> for TraitClause {
    type View = SpannedTraitClauseView;

    fn decode(value: &Self, span_info: SpannedInfo, tcx: &TyCtxt) -> Self::View {
        match *value {
            TraitClause::Outlives(re) => {
                SpannedTraitClauseView::Outlives(Spanned::new_raw(re, span_info.unwrap(tcx)))
            }
            TraitClause::Trait(spec) => {
                SpannedTraitClauseView::Trait(Spanned::new_raw(spec, span_info.unwrap(tcx)))
            }
        }
    }
}

impl SpannedViewEncode<TyCtxt> for SpannedTraitClauseView {
    type Unspanned = TraitClause;

    fn encode(self, own_span: Span, tcx: &TyCtxt) -> Spanned<Self::Unspanned> {
        match self {
            SpannedTraitClauseView::Outlives(re) => Spanned::new_raw(
                TraitClause::Outlives(re.value),
                re.span_info.wrap(own_span, tcx),
            ),
            SpannedTraitClauseView::Trait(spec) => Spanned::new_raw(
                TraitClause::Trait(spec.value),
                spec.span_info.wrap(own_span, tcx),
            ),
        }
    }
}

// === TraitParam === //

pub type SpannedTraitParam = Spanned<TraitParam>;

#[derive(Debug, Copy, Clone)]
pub enum SpannedTraitParamView {
    Equals(SpannedTyOrRe),
    Unspecified(SpannedTraitClauseList),
}

impl SpannedViewDecode<TyCtxt> for TraitParam {
    type View = SpannedTraitParamView;

    fn decode(value: &Self, span_info: SpannedInfo, tcx: &TyCtxt) -> Self::View {
        match *value {
            TraitParam::Equals(ty_or_re) => {
                SpannedTraitParamView::Equals(Spanned::new_raw(ty_or_re, span_info.unwrap(tcx)))
            }
            TraitParam::Unspecified(clauses) => {
                SpannedTraitParamView::Unspecified(Spanned::new_raw(clauses, span_info.unwrap(tcx)))
            }
        }
    }
}

impl SpannedViewEncode<TyCtxt> for SpannedTraitParamView {
    type Unspanned = TraitParam;

    fn encode(self, own_span: Span, tcx: &TyCtxt) -> Spanned<Self::Unspanned> {
        match self {
            SpannedTraitParamView::Equals(ty_or_re) => Spanned::new_raw(
                TraitParam::Equals(ty_or_re.value),
                ty_or_re.span_info.wrap(own_span, tcx),
            ),
            SpannedTraitParamView::Unspecified(clauses) => Spanned::new_raw(
                TraitParam::Unspecified(clauses.value),
                clauses.span_info.wrap(own_span, tcx),
            ),
        }
    }
}

// === AdtInstance === //

pub type SpannedAdtInstance = Spanned<AdtInstance>;

#[derive(Debug, Copy, Clone)]
pub struct SpannedAdtInstanceView {
    pub def: Obj<AdtItem>,
    pub params: SpannedTyOrReList,
}

impl SpannedViewDecode<TyCtxt> for AdtInstance {
    type View = SpannedAdtInstanceView;

    fn decode(value: &Self, span_info: SpannedInfo, tcx: &TyCtxt) -> Self::View {
        SpannedAdtInstanceView {
            def: value.def,
            params: Spanned::new_raw(value.params, span_info.unwrap(tcx)),
        }
    }
}

impl SpannedViewEncode<TyCtxt> for SpannedAdtInstanceView {
    type Unspanned = AdtInstance;

    fn encode(self, own_span: Span, tcx: &TyCtxt) -> Spanned<Self::Unspanned> {
        Spanned::new_raw(
            AdtInstance {
                def: self.def,
                params: self.params.value,
            },
            self.params.span_info.wrap(own_span, tcx),
        )
    }
}

// === TraitSpec === //

pub type SpannedTraitSpec = Spanned<TraitSpec>;

#[derive(Debug, Copy, Clone)]
pub struct SpannedTraitSpecView {
    pub def: Obj<TraitItem>,
    pub params: SpannedTraitParamList,
}

impl SpannedViewDecode<TyCtxt> for TraitSpec {
    type View = SpannedTraitSpecView;

    fn decode(value: &Self, span_info: SpannedInfo, tcx: &TyCtxt) -> Self::View {
        SpannedTraitSpecView {
            def: value.def,
            params: Spanned::new_raw(value.params, span_info.unwrap(tcx)),
        }
    }
}

impl SpannedViewEncode<TyCtxt> for SpannedTraitSpecView {
    type Unspanned = TraitSpec;

    fn encode(self, own_span: Span, tcx: &TyCtxt) -> Spanned<Self::Unspanned> {
        Spanned::new_raw(
            TraitSpec {
                def: self.def,
                params: self.params.value,
            },
            self.params.span_info.wrap(own_span, tcx),
        )
    }
}

// === TraitInstance === //

pub type SpannedTraitInstance = Spanned<TraitInstance>;

#[derive(Debug, Copy, Clone)]
pub struct SpannedTraitInstanceView {
    pub def: Obj<TraitItem>,
    pub params: SpannedTyOrReList,
}

impl SpannedViewDecode<TyCtxt> for TraitInstance {
    type View = SpannedTraitInstanceView;

    fn decode(value: &Self, span_info: SpannedInfo, tcx: &TyCtxt) -> Self::View {
        SpannedTraitInstanceView {
            def: value.def,
            params: Spanned::new_raw(value.params, span_info.unwrap(tcx)),
        }
    }
}

impl SpannedViewEncode<TyCtxt> for SpannedTraitInstanceView {
    type Unspanned = TraitInstance;

    fn encode(self, own_span: Span, tcx: &TyCtxt) -> Spanned<Self::Unspanned> {
        Spanned::new_raw(
            TraitInstance {
                def: self.def,
                params: self.params.value,
            },
            self.params.span_info.wrap(own_span, tcx),
        )
    }
}

// === TyProjection === //

pub type SpannedTyProjection = Spanned<TyProjection>;

#[derive(Debug, Copy, Clone)]
pub struct SpannedTyProjectionView {
    pub target: SpannedTy,
    pub spec: SpannedTraitSpec,
    pub assoc_span: Option<Span>,
    pub assoc: u32,
}

impl SpannedViewDecode<TyCtxt> for TyProjection {
    type View = SpannedTyProjectionView;

    fn decode(value: &Self, span_info: SpannedInfo, tcx: &TyCtxt) -> Self::View {
        let [target_span, spec_span, assoc_span] = span_info.child_spans(tcx);

        SpannedTyProjectionView {
            target: Spanned::new_raw(value.target, target_span),
            spec: Spanned::new_raw(value.spec, spec_span),
            assoc_span: assoc_span.own_span(),
            assoc: value.assoc,
        }
    }
}

impl SpannedViewEncode<TyCtxt> for SpannedTyProjectionView {
    type Unspanned = TyProjection;

    fn encode(self, own_span: Span, tcx: &TyCtxt) -> Spanned<Self::Unspanned> {
        Spanned::new_raw(
            TyProjection {
                target: self.target.value,
                spec: self.spec.value,
                assoc: self.assoc,
            },
            SpannedInfo::new_list(
                own_span,
                &[
                    self.target.span_info,
                    self.spec.span_info,
                    SpannedInfo::new_maybe_terminal(self.assoc_span, tcx),
                ],
                tcx,
            ),
        )
    }
}
