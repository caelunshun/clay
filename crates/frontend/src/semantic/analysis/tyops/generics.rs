use crate::{
    base::{
        analysis::Spanned,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    semantic::{
        analysis::{TyCtxt, TyVisitor, TyVisitorUnspanned},
        syntax::{
            AnyGeneric, GenericBinder, PosInBinder, RegionGeneric, SpannedTraitClauseList,
            TraitClause, TraitParam, TraitSpec, TyKind, TyOrRe, TypeGeneric,
        },
    },
    symbol,
};
use derive_where::derive_where;
use std::{marker::PhantomData, ops::ControlFlow};

impl TyCtxt {
    pub fn seal_generic_binder(&self, binder: GenericBinder) -> Obj<GenericBinder> {
        let s = &self.session;

        let binder = Obj::new(binder, s);

        for (i, generic) in binder.r(s).generics.iter().enumerate() {
            LateInit::init(
                match generic {
                    AnyGeneric::Re(generic) => &generic.r(s).binder,
                    AnyGeneric::Ty(generic) => &generic.r(s).binder,
                },
                PosInBinder {
                    def: binder,
                    idx: i as u32,
                },
            );
        }

        binder
    }

    pub fn mentioned_generics<B>(
        &self,
        ty: TyOrRe,
        f: impl FnMut(AnyGeneric) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        GenericMentionVisitor {
            _ty: PhantomData,
            tcx: self,
            f,
        }
        .visit_ty_or_re(ty)
    }

    pub fn elaborate_generic_clauses(
        &self,
        generic: Obj<TypeGeneric>,
        binder: &mut GenericBinder,
    ) -> SpannedTraitClauseList {
        let s = &self.session;

        let generic = generic.r(s);

        if let Some(v) = LateInit::get(&generic.elaborated_clauses) {
            return *v;
        }

        let clauses = generic
            .user_clauses
            .value
            .r(s)
            .iter()
            .map(|clause| match *clause {
                TraitClause::Outlives(re) => TraitClause::Outlives(re),
                TraitClause::Trait(spec) => {
                    let params = spec
                        .params
                        .r(s)
                        .iter()
                        .zip(&spec.def.r(s).generics.r(s).generics)
                        .map(|(&param, def)| {
                            let clauses = match param {
                                TraitParam::Equals(_) => return param,
                                TraitParam::Unspecified(clauses) => self.join_trait_clause_lists(
                                    // TODO: These require some substitutions and super-traits
                                    //  should be revealed.
                                    def.unwrap_ty().r(s).user_clauses.value,
                                    clauses,
                                ),
                            };

                            // TODO: Better debug names.
                            let generic = Obj::new(
                                TypeGeneric {
                                    span: Span::DUMMY,
                                    ident: Ident {
                                        span: Span::DUMMY,
                                        text: symbol!("?"),
                                        raw: false,
                                    },
                                    binder: LateInit::uninit(),
                                    user_clauses: LateInit::new(Spanned::new_unspanned(clauses)),
                                    elaborated_clauses: LateInit::uninit(),
                                    is_synthetic: true,
                                },
                                s,
                            );

                            binder.generics.push(AnyGeneric::Ty(generic));

                            TraitParam::Equals(TyOrRe::Ty(
                                self.intern_ty(TyKind::Universal(generic)),
                            ))
                        })
                        .collect::<Vec<_>>();

                    TraitClause::Trait(TraitSpec {
                        def: spec.def,
                        params: self.intern_trait_param_list(&params),
                    })
                }
            })
            .collect::<Vec<_>>();

        let clauses = self.intern_trait_clause_list(&clauses);

        // TODO: Inherit spans
        let clauses = Spanned::new_unspanned(clauses);

        LateInit::init(&generic.elaborated_clauses, clauses);

        clauses
    }
}

#[derive_where(Copy, Clone; F)]
pub struct GenericMentionVisitor<'tcx, F, B> {
    _ty: PhantomData<fn() -> B>,
    tcx: &'tcx TyCtxt,
    f: F,
}

impl<'tcx, F, B> GenericMentionVisitor<'tcx, F, B>
where
    F: FnMut(AnyGeneric) -> ControlFlow<B>,
{
    pub fn new(tcx: &'tcx TyCtxt, f: F) -> Self {
        Self {
            _ty: PhantomData,
            tcx,
            f,
        }
    }
}

impl<'tcx, F, B> TyVisitor<'tcx> for GenericMentionVisitor<'tcx, F, B>
where
    F: FnMut(AnyGeneric) -> ControlFlow<B>,
{
    type Break = B;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    fn visit_spanned_re_generic_use(
        &mut self,
        _span: Option<Span>,
        generic: Obj<RegionGeneric>,
    ) -> ControlFlow<Self::Break> {
        (self.f)(AnyGeneric::Re(generic))
    }

    fn visit_spanned_ty_generic_use(
        &mut self,
        _span: Option<Span>,
        generic: Obj<TypeGeneric>,
    ) -> ControlFlow<Self::Break> {
        (self.f)(AnyGeneric::Ty(generic))
    }
}
