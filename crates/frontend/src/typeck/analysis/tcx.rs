use crate::{
    base::{
        Session,
        arena::{ObjInterner, ObjListInterner},
    },
    typeck::syntax::{Instance, InstanceInner, Ty, TyKind, TyList},
    utils::hash::FxHashSet,
};
use std::{cell::RefCell, ops::Deref, rc::Rc};

#[derive(Debug, Clone)]
pub struct TyCtxt {
    inner: Rc<TyCtxtInner>,
}

#[derive(Debug)]
pub struct TyCtxtInner {
    pub session: Session,
    pub ty_interner: ObjInterner<TyKind>,
    pub ty_list_interner: ObjListInterner<Ty>,
    pub instance_interner: ObjInterner<InstanceInner>,
    pub wf_state: RefCell<WfState>,
    pub queries: Queries,
}

#[derive(Debug, Default)]
pub struct WfState {
    pub validated: FxHashSet<WfRequirement>,
    pub queue: Vec<WfRequirement>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum WfRequirement {}

#[derive(Debug, Default)]
pub struct Queries {}

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
                ty_interner: ObjInterner::default(),
                ty_list_interner: ObjListInterner::default(),
                instance_interner: ObjInterner::default(),
                wf_state: RefCell::default(),
                queries: Queries::default(),
            }),
        }
    }

    pub fn intern_ty(&self, ty: TyKind) -> Ty {
        Ty::new_unchecked(self.ty_interner.intern(ty, &self.session))
    }

    pub fn intern_tys(&self, ty: &[Ty]) -> TyList {
        TyList::new_unchecked(self.ty_list_interner.intern(ty, &self.session))
    }

    pub fn intern_instance(&self, instance: InstanceInner) -> Instance {
        Instance::new_unchecked(self.instance_interner.intern(instance, &self.session))
    }

    pub fn queue_wf(&self, req: WfRequirement) {
        let mut state = self.wf_state.borrow_mut();

        if state.validated.insert(req) {
            state.queue.push(req);
        }
    }

    #[expect(clippy::never_loop)]
    pub fn flush_wf(&self) {
        let s = &self.session;

        loop {
            let Some(req) = self.wf_state.borrow_mut().queue.pop() else {
                break;
            };

            match req {}
        }
    }
}
