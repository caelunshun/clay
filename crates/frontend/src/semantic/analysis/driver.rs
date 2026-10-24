use crate::{
    base::{ErrorGuaranteed, arena::Obj},
    semantic::{
        analysis::sigck::CrateSigckVisitor,
        infer::ImplCache,
        syntax::{AttributeKind, Crate, EarlyAttrLang, TyCtxt},
    },
};

pub fn check_crate(tcx: &TyCtxt, krate: Obj<Crate>) {
    let s = &tcx.session;

    // Populate implementation cache
    let mut impl_cache = ImplCache::default();
    impl_cache.populate(tcx, krate);

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
        impl_cache: &impl_cache,
        krate,
    }
    .visit_crate();
}
