pub mod std {
    #[lang("deref_trait")]
    pub trait Deref {
        type Target;
    }

    impl<'a, T: &longer 'a> Deref for &'a T {
        type Target = T;
    }

    impl<'a, T: &longer 'a> Deref for &'a mut T {
        type Target = T;
    }

    #[lang("fn_once_trait")]
    pub trait FnOnce<I, O> {}

    #[lang("fn_mut_trait")]
    pub trait FnMut<I, O>: FnOnce<I, O> {}

    #[lang("fn_trait")]
    pub trait Fn<I, O>: FnMut<I, O> {}
}

use std::*;

struct Foo;

struct Bar;

impl Deref for Bar {
    type Target = Foo;
}

struct Baz;

impl Deref for Baz {
    type Target = Foo;
}

pub trait Meow {}

impl<T> Meow for T {}

fn demo<
    F: for<T: Meow> FnOnce<(T,), T>,
    G: for<F: for<'a, T: &longer 'a> FnOnce<(&'a T,), &'a T>> FnOnce<(F,), F>,
>(
    f: F,
    g: G,
) {
    let a: Bar;
    let b: Baz;

    let foo = if true {
        &a
    } else {
        g(f)(&b)
    };

    let hehe = meow;

    if hehe(true) {
        hehe(&a)
    } else {
        hehe(&b)
    }

    let early_bound = meow::<_>;
    let funky = early_bound.as::<&'gc dyn for<T: Meow> FnOnce<(T,), T>>;
    early_bound('a');

    let late_bound = meow;
    let funky = late_bound.as::<&'gc dyn for<T: Meow> FnOnce<(T,), T>>;
    late_bound('a');
}

fn meow<T>(v: T) -> T {
    v
}
