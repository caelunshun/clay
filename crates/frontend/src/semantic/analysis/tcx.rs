use crate::{
    base::{
        HasSession, Session,
        analysis::SpannedInfo,
        arena::{HasInterner, HasListInterner, Interner, ListInterner, Obj},
    },
    semantic::{
        analysis::{CoherenceMap, CrateTypeckVisitor},
        syntax::{
            Crate, HrtbDebruijnDef, TraitClause, TraitClauseList, TraitParam, Ty, TyKind, TyOrRe,
            TyShape,
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
    pub hrtb_debruijn_list: ListInterner<HrtbDebruijnDef>,
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
            }),
        }
    }

    pub fn check_crate(&self, krate: Obj<Crate>) {
        let s = &self.session;

        let mut coherence = CoherenceMap::default();

        coherence.populate(self, krate);

        for &def in &**krate.r(s).items {
            let Some(def) = def.r(s).kind.as_impl() else {
                continue;
            };

            self.check_impl_generic_covering(def);
        }

        CrateTypeckVisitor {
            tcx: self,
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

impl HasListInterner<HrtbDebruijnDef> for TyCtxt {
    fn interner(&self) -> &ListInterner<HrtbDebruijnDef> {
        &self.interners.hrtb_debruijn_list
    }
}
