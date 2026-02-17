use crate::{
    base::arena::{HasInterner as _, HasListInterner as _},
    semantic::{
        analysis::{ClauseCx, ClauseErrorProbe, ClauseOrigin},
        syntax::{HrtbUniverse, TraitParam, TraitSpec, Ty, TyKind, TyOrRe},
    },
};

pub fn attempt_deref(ccx: &mut ClauseCx<'_>, curr: Ty) -> Option<Ty> {
    let mut fork = ccx.clone().with_silent();

    let res = attempt_deref_clobber_obligations(&mut fork, curr);

    if res.is_some() {
        *ccx = fork;
    }

    res
}

pub fn attempt_deref_clobber_obligations(ccx: &mut ClauseCx<'_>, curr: Ty) -> Option<Ty> {
    let s = ccx.session();
    let tcx = ccx.tcx();
    let krate = ccx.krate();

    let next_infer_var = ccx.fresh_ty_infer_var(HrtbUniverse::ROOT);
    let next_infer = tcx.intern(TyKind::InferVar(next_infer_var));

    // This probing routine works by attempting to resolve an obligation as much as possible and
    // bailing out if an error occurs.
    //
    // Doing this roughly matches `rustc`'s behavior...
    //
    // ```
    // use core::ops::Deref;
    //
    // pub struct Foo;
    //
    // pub struct Bar<T>([T; 0]);
    //
    // impl<T> Bar<T> {
    //     fn bind(&self, _: T) {}
    // }
    //
    // impl<T: Copy> Deref for Bar<T> {
    //     type Target = Foo;
    //
    //     fn deref(&self) -> &Foo {
    //         &Foo
    //     }
    // }
    //
    // // Okay!
    // fn example_1() {
    //     let bar = &Bar::<_>([]);
    //     [&Foo, bar];
    //
    //     bar.bind(3i32);
    // }
    //
    // // No coercion is performed.
    // fn example_2() {
    //     let bar = &Bar::<_>([]);
    //     bar.bind(Vec::new());
    //     [&Foo, bar];
    // }
    //
    // // We complain about `Vec` not being `Copy`.
    // fn example_3() {
    //     let bar = &Bar::<_>([]);
    //     [&Foo, bar];
    //     bar.bind(Vec::new());
    // }
    // ```
    let probe = ClauseErrorProbe::default();

    ccx.oblige_ty_meets_trait_instantiated(
        ClauseOrigin::never_printed().with_probe_sink(probe.clone()),
        curr,
        TraitSpec {
            def: krate.r(s).deref_lang_item(s).unwrap(),
            params: tcx.intern_list(&[TraitParam::Equals(TyOrRe::Ty(next_infer))]),
        },
        HrtbUniverse::ROOT,
    );

    ccx.poll_obligations();

    if probe.had_error() {
        return None;
    }

    let Ok(resolved) = ccx.lookup_ty_infer_var_after_poll(next_infer_var) else {
        return None;
    };

    Some(resolved)
}
