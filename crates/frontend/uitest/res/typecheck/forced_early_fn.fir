#[lang("fn_once_trait")]
pub trait FnOnce<I, O> {}

#[lang("fn_mut_trait")]
pub trait FnMut<I, O>: FnOnce<I, O> {}

#[lang("fn_trait")]
pub trait Fn<I, O>: FnMut<I, O> {}

fn meow<Q>() {}

fn foo<F: Fn<(), ()>>(f: F) {}

fn main() {
    // FIXME: should be rejected
    meow();

    // FIXME: should be rejected
    foo(meow);
}
