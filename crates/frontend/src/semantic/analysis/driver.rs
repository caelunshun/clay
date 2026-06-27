use crate::{
    base::{ErrorGuaranteed, arena::Obj},
    semantic::{
        analysis::sigck::CrateSigckVisitor,
        infer::CoherenceMap,
        syntax::{AttributeKind, Crate, EarlyAttrLang, TyCtxt},
    },
};

pub fn check_crate(tcx: &TyCtxt, krate: Obj<Crate>) {
    let s = &tcx.session;

    // Compute coherence
    let mut coherence = CoherenceMap::default();
    coherence.populate(tcx, krate);

    // Discover language items
    for &def in &**krate.r(s).items {
        for attr in &**def.r(s).attrs {
            let AttributeKind::Lang(EarlyAttrLang { name }) = attr.r(s).kind else {
                continue;
            };

            let (Ok(()) | Err(ErrorGuaranteed)) =
                krate.r(s).lang_items.define(tcx, name, attr.r(s).span, def);
        }
    }

    // Signature-check crate
    CrateSigckVisitor {
        tcx,
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
