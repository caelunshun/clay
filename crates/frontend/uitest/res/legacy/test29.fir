pub mod std {
    #[lang("fn_once_trait")]
    pub trait FnOnce<I, O> {}

    #[lang("fn_mut_trait")]
    pub trait FnMut<I, O>: FnOnce<I, O> {}

    #[lang("fn_trait")]
    pub trait Fn<I, O>: FnMut<I, O> {}
}

trait Trait<T> {}

fn foo() -> &'gc dyn for<T> Trait<(T,)> {
    loop {}
}

fn bar<V>(v: V) -> &'gc dyn for<T> Trait<(V,)> {
    loop {}
}

fn make_infer<T>() -> T {
    loop {}
}

fn main() {
    let infer = make_infer::<_>();
    let lhs = (foo(),);
    let rhs = (bar(infer),);
    if true { lhs } else { rhs };
    infer  // Must not leak an `HrtbVar` type.
}
