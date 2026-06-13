use crate::{
    base::{ErrorGuaranteed, arena::Obj},
    semantic::{
        analysis::{CrateBorrowCheckVisitor, CrateTypeckVisitor},
        infer::CoherenceMap,
        syntax::{AttributeKind, Crate, EarlyAttrLang, TyCtxt},
    },
};

impl TyCtxt {
    pub fn check_crate(&self, krate: Obj<Crate>) {
        let s = &self.session;

        // Compute coherence
        let mut coherence = CoherenceMap::default();
        coherence.populate(self, krate);

        // Discover language items
        for &def in &**krate.r(s).items {
            for attr in &**def.r(s).attrs {
                let AttributeKind::Lang(EarlyAttrLang { name }) = attr.r(s).kind else {
                    continue;
                };

                let (Ok(()) | Err(ErrorGuaranteed)) =
                    krate
                        .r(s)
                        .lang_items
                        .define(self, name, attr.r(s).span, def);
            }
        }

        // Type-check crate
        CrateTypeckVisitor {
            tcx: self,
            coherence: &coherence,
            krate,
        }
        .visit_crate();

        // // Borrow-check crate
        // CrateBorrowCheckVisitor {
        //     tcx: self,
        //     krate,
        //     coherence: &coherence,
        // }
        // .visit_crate();
    }
}
