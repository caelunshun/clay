use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::{MirDataflowFacts, MirLowerCtxt, TyCtxt},
        syntax::{Crate, FnDef, ItemKind},
    },
};

pub struct CrateBorrowCheckVisitor<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub krate: Obj<Crate>,
}

impl<'tcx> CrateBorrowCheckVisitor<'tcx> {
    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn visit_crate(&mut self) {
        let s = self.session();

        for &item in self.krate.r(s).items.iter() {
            match *item.r(s).kind {
                ItemKind::Fn(def) => {
                    self.visit_fn_def(*def.r(s).def);
                }
                ItemKind::Trait(def) => {
                    for &method in def.r(s).methods.iter() {
                        self.visit_fn_def(method);
                    }
                }
                ItemKind::Impl(def) => {
                    for &method in def.r(s).methods.iter() {
                        let Some(method) = method else {
                            continue;
                        };

                        self.visit_fn_def(method);
                    }
                }

                ItemKind::Module(..)
                | ItemKind::Adt(..)
                | ItemKind::EnumVariant(..)
                | ItemKind::TypeAlias(..) => {
                    // (no bodies)
                }
            }
        }
    }

    pub fn visit_fn_def(&self, def: Obj<FnDef>) {
        let s = self.session();

        if def.r(s).hir_body.is_none() {
            return;
        }

        let mut ctxt = MirLowerCtxt::new(self.tcx, def);
        ctxt.lower_entry();

        let df = MirDataflowFacts::compute(self.tcx, &ctxt.body);
        dbg!(df);
    }
}
