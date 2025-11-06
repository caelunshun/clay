use crate::{
    base::{
        Session,
        analysis::Memo,
        arena::{Interner, ListInterner, Obj},
    },
    semantic::{
        analysis::ImplFreshInfer,
        syntax::{
            GenericInstance, ImplDef, InferTyVar, ListOfTraitClauseList, TraitClause,
            TraitClauseList, TraitParam, TraitParamList, Ty, TyKind, TyList, TyOrRe, TyOrReList,
        },
    },
};
use std::{ops::Deref, rc::Rc};

#[derive(Debug, Clone)]
pub struct TyCtxt {
    inner: Rc<TyCtxtInner>,
}

#[derive(Debug)]
pub struct TyCtxtInner {
    pub session: Session,
    pub interners: Interners,
    pub queries: Queries,
}

#[derive(Debug, Default)]
pub struct Interners {
    pub ty: Interner<TyKind>,
    pub ty_list: ListInterner<Ty>,
    pub ty_or_re_list: ListInterner<TyOrRe>,
    pub trait_param_list: ListInterner<TraitParam>,
    pub trait_clause_list: ListInterner<TraitClause>,
    pub list_of_trait_clause_list: ListInterner<TraitClauseList>,
}

#[derive(Debug, Default)]
pub struct Queries {
    pub substitute_ty: Memo<(Ty, Ty, GenericInstance), Ty>,
    pub substitute_ty_list: Memo<(TyList, Ty, GenericInstance), TyList>,
    pub substitute_ty_or_re_list: Memo<(TyOrReList, Ty, GenericInstance), TyOrReList>,
    pub substitute_clause_list: Memo<(TraitClauseList, Ty, GenericInstance), TraitClauseList>,
    pub substitute_trait_param_list: Memo<(TraitParamList, Ty, GenericInstance), TraitParamList>,
    pub instantiate_fresh_target_infers: Memo<(Obj<ImplDef>, InferTyVar), ImplFreshInfer>,
}

impl Deref for TyCtxt {
    type Target = TyCtxtInner;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl TyCtxt {
    pub fn new(session: Session) -> Self {
        Self {
            inner: Rc::new(TyCtxtInner {
                session,
                interners: Interners::default(),
                queries: Queries::default(),
            }),
        }
    }

    pub fn intern_ty(&self, ty: TyKind) -> Ty {
        self.interners.ty.intern(ty, &self.session)
    }

    pub fn intern_tys(&self, ty: &[Ty]) -> TyList {
        self.interners.ty_list.intern(ty, &self.session)
    }

    pub fn intern_ty_or_re_list(&self, elems: &[TyOrRe]) -> TyOrReList {
        self.interners.ty_or_re_list.intern(elems, &self.session)
    }

    pub fn intern_trait_param_list(&self, elems: &[TraitParam]) -> TraitParamList {
        self.interners.trait_param_list.intern(elems, &self.session)
    }

    pub fn intern_trait_clause_list(&self, elems: &[TraitClause]) -> TraitClauseList {
        self.interners
            .trait_clause_list
            .intern(elems, &self.session)
    }

    pub fn intern_list_of_trait_clause_list(
        &self,
        elems: &[TraitClauseList],
    ) -> ListOfTraitClauseList {
        self.interners
            .list_of_trait_clause_list
            .intern(elems, &self.session)
    }

    pub fn join_trait_clause_lists(
        &self,
        lhs: TraitClauseList,
        rhs: TraitClauseList,
    ) -> TraitClauseList {
        let s = &self.session;

        if lhs.r(s).is_empty() {
            return rhs;
        }

        if rhs.r(s).is_empty() {
            return lhs;
        }

        self.intern_trait_clause_list(
            &[lhs.r(s).iter().copied(), rhs.r(s).iter().copied()]
                .into_iter()
                .flatten()
                .collect::<Vec<_>>(),
        )
    }
}
