use crate::{
    base::{ErrorGuaranteed, Obj, Session},
    semantic::{
        analysis::sigck::CrateSigckVisitor,
        infer::ImplCache,
        syntax::{AttributeKind, Crate, EarlyAttrLang},
    },
};

pub fn check_crate(s: &Session, krate: Obj<Crate>) {
    // Populate implementation cache
    let mut impl_cache = ImplCache::default();
    impl_cache.populate(s, krate);

    // Discover language items
    for &def in &**krate.r(s).items {
        for attr in &**def.r(s).attrs {
            let AttributeKind::Lang(EarlyAttrLang { name }) = attr.r(s).kind else {
                continue;
            };

            let (Ok(()) | Err(ErrorGuaranteed)) =
                krate.r(s).lang_items.define(s, name, attr.r(s).span, def);
        }
    }

    // Signature-check crate
    CrateSigckVisitor {
        session: s,
        impl_cache: &impl_cache,
        krate,
    }
    .visit_crate();
}
