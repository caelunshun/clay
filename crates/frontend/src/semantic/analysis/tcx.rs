use crate::{
    base::{
        HasSession, Session,
        analysis::{Memo, SpannedInfo},
        arena::{HasInterner, HasListInterner, Interner, ListInterner, Obj},
    },
    semantic::{
        analysis::{BinderSubstitution, CoherenceMap, CrateTypeckVisitor},
        syntax::{
            Crate, ListOfTraitClauseList, TraitClause, TraitClauseList, TraitParam, TraitParamList,
            Ty, TyKind, TyList, TyOrRe, TyOrReList, TyShape,
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
    pub spanned_info_list: ListInterner<SpannedInfo>,
    pub coherence_ty_list: ListInterner<TyShape>,
}

#[derive(Debug, Default)]
pub struct Queries {
    pub substitute_ty: Memo<(Ty, Ty, Option<BinderSubstitution>), Ty>,
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

    pub fn intern_ty_list(&self, ty: &[Ty]) -> TyList {
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

    pub fn check_crate(&self, krate: Obj<Crate>) {
        let s = &self.session;

        let mut coherence = CoherenceMap::default();

        coherence.populate(self, krate);

        for &def in &**krate.r(s).items {
            let Some(def) = def.r(s).kind.as_impl() else {
                continue;
            };

            self.determine_impl_generic_solve_order(def);
        }

        _ = CrateTypeckVisitor {
            tcx: self,
            self_ty: None,
            clause_applies_to: None,
            coherence: &coherence,
        }
        .visit_crate(krate);
    }
}

impl HasSession for TyCtxt {
    fn session(&self) -> &Session {
        &self.session
    }
}

impl HasInterner<TyKind> for TyCtxt {
    fn interner(&self) -> &Interner<TyKind> {
        &self.interners.ty
    }
}

impl HasListInterner<Ty> for TyCtxt {
    fn interner(&self) -> &ListInterner<Ty> {
        &self.interners.ty_list
    }
}

impl HasListInterner<TyOrRe> for TyCtxt {
    fn interner(&self) -> &ListInterner<TyOrRe> {
        &self.interners.ty_or_re_list
    }
}

impl HasListInterner<TraitParam> for TyCtxt {
    fn interner(&self) -> &ListInterner<TraitParam> {
        &self.interners.trait_param_list
    }
}

impl HasListInterner<TraitClause> for TyCtxt {
    fn interner(&self) -> &ListInterner<TraitClause> {
        &self.interners.trait_clause_list
    }
}

impl HasListInterner<TraitClauseList> for TyCtxt {
    fn interner(&self) -> &ListInterner<TraitClauseList> {
        &self.interners.list_of_trait_clause_list
    }
}

impl HasListInterner<SpannedInfo> for TyCtxt {
    fn interner(&self) -> &ListInterner<SpannedInfo> {
        &self.interners.spanned_info_list
    }
}

impl HasListInterner<TyShape> for TyCtxt {
    fn interner(&self) -> &ListInterner<TyShape> {
        &self.interners.coherence_ty_list
    }
}
