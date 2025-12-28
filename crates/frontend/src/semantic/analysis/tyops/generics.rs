use crate::{
    base::{
        analysis::Spanned,
        arena::{HasInterner, HasListInterner, LateInit, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    semantic::{
        analysis::{TyCtxt, TyVisitable, TyVisitor, TyVisitorExt},
        syntax::{
            AnyGeneric, GenericBinder, PosInBinder, Re, RegionGeneric, SpannedTraitClauseList,
            TraitClause, TraitClauseList, TraitInstance, TraitParam, TraitSpec, TyKind, TyOrRe,
            TyOrReList, TypeGeneric,
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

        for (i, generic) in binder.r(s).defs.iter().enumerate() {
            LateInit::init(
                match generic {
                    AnyGeneric::Re(generic) => &generic.r(s).binder,
                    AnyGeneric::Ty(generic) => &generic.r(s).binder,
                },
                Some(PosInBinder {
                    def: binder,
                    idx: i as u32,
                }),
            );
        }

        binder
    }

    pub fn clone_generic_binder_without_clauses(
        &self,
        orig_binder: Obj<GenericBinder>,
    ) -> Obj<GenericBinder> {
        let s = &self.session;

        let new_binder_defs = orig_binder
            .r(s)
            .defs
            .iter()
            .map(|&def| match def {
                AnyGeneric::Re(generic) => AnyGeneric::Re(Obj::new(
                    RegionGeneric {
                        span: generic.r(s).span,
                        lifetime: generic.r(s).lifetime,
                        binder: LateInit::uninit(),
                        clauses: LateInit::uninit(),
                        is_synthetic: true,
                    },
                    s,
                )),
                AnyGeneric::Ty(generic) => AnyGeneric::Ty(Obj::new(
                    TypeGeneric {
                        span: generic.r(s).span,
                        ident: generic.r(s).ident,
                        binder: LateInit::uninit(),
                        user_clauses: LateInit::uninit(),
                        elaborated_clauses: LateInit::uninit(),
                        is_synthetic: true,
                    },
                    s,
                )),
            })
            .collect::<Vec<_>>();

        self.seal_generic_binder(GenericBinder {
            defs: new_binder_defs,
        })
    }

    pub fn init_generic_binder_clauses_of_duplicate(
        &self,
        orig_binder: Obj<GenericBinder>,
        new_binder: Obj<GenericBinder>,
        mut subst: impl FnMut(SpannedTraitClauseList) -> SpannedTraitClauseList,
    ) -> Obj<GenericBinder> {
        let s = &self.session;

        for (new_generic, old_generic) in new_binder.r(s).defs.iter().zip(&orig_binder.r(s).defs) {
            match (new_generic, old_generic) {
                (AnyGeneric::Re(new_generic), AnyGeneric::Re(old_generic)) => {
                    LateInit::init(&new_generic.r(s).clauses, subst(*old_generic.r(s).clauses));
                }
                (AnyGeneric::Ty(new_generic), AnyGeneric::Ty(old_generic)) => {
                    LateInit::init(
                        &new_generic.r(s).user_clauses,
                        subst(*old_generic.r(s).user_clauses),
                    );
                }
                _ => unreachable!(),
            }
        }

        new_binder
    }

    pub fn substitute_generic_binder_clauses(
        &self,
        orig_binder: Obj<GenericBinder>,
        subst: impl FnMut(SpannedTraitClauseList) -> SpannedTraitClauseList,
    ) -> Obj<GenericBinder> {
        let new_binder = self.clone_generic_binder_without_clauses(orig_binder);
        self.init_generic_binder_clauses_of_duplicate(orig_binder, new_binder, subst);

        new_binder
    }

    pub fn convert_generic_binder_into_instance_args(
        &self,
        binder: Obj<GenericBinder>,
    ) -> TyOrReList {
        let s = &self.session;

        self.intern_list(
            &binder
                .r(s)
                .defs
                .iter()
                .map(|generic| match generic {
                    AnyGeneric::Re(generic) => TyOrRe::Re(Re::Universal(*generic)),
                    AnyGeneric::Ty(generic) => TyOrRe::Ty(self.intern(TyKind::Universal(*generic))),
                })
                .collect::<Vec<_>>(),
        )
    }

    pub fn convert_trait_instance_to_spec(&self, instance: TraitInstance) -> TraitSpec {
        TraitSpec {
            def: instance.def,
            params: self.intern_list(
                &instance
                    .params
                    .r(&self.session)
                    .iter()
                    .map(|&arg| TraitParam::Equals(arg))
                    .collect::<Vec<_>>(),
            ),
        }
    }

    pub fn mentioned_generics<B>(
        &self,
        ty: impl TyVisitable,
        f: impl FnMut(AnyGeneric) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        GenericMentionVisitor {
            _ty: PhantomData,
            tcx: self,
            f,
        }
        .visit_fallible(ty)
    }

    pub fn elaborate_generic_clauses(
        &self,
        generic: Obj<TypeGeneric>,
        mut binder: Option<&mut GenericBinder>,
    ) -> TraitClauseList {
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
                        .zip(&spec.def.r(s).generics.r(s).defs)
                        .map(|(&param, def)| {
                            let clauses = match param {
                                TraitParam::Equals(_) => return param,
                                // TODO: Actually elaborate :)
                                TraitParam::Unspecified(clauses) => clauses,
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

                            if let Some(binder) = &mut binder {
                                binder.defs.push(AnyGeneric::Ty(generic));
                            }

                            TraitParam::Equals(TyOrRe::Ty(self.intern(TyKind::Universal(generic))))
                        })
                        .collect::<Vec<_>>();

                    TraitClause::Trait(TraitSpec {
                        def: spec.def,
                        params: self.intern_list(&params),
                    })
                }
            })
            .collect::<Vec<_>>();

        let clauses = self.intern_list(&clauses);

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

    fn visit_re_generic_use(
        &mut self,
        _span: Option<Span>,
        generic: Obj<RegionGeneric>,
    ) -> ControlFlow<Self::Break> {
        (self.f)(AnyGeneric::Re(generic))
    }

    fn visit_ty_generic_use(
        &mut self,
        _span: Option<Span>,
        generic: Obj<TypeGeneric>,
    ) -> ControlFlow<Self::Break> {
        (self.f)(AnyGeneric::Ty(generic))
    }
}
