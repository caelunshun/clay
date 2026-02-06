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

fn demo<
    F: for<T> FnOnce<(T,), T>,
    G: for<F: for<'a, T: &shorter 'a> FnOnce<(&'a T,), &'a T>> FnOnce<(F,), F>,
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
}
