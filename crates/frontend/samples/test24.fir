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
}

pub trait Meow {
    type Hey;

    fn obtain(me: Self) -> <Self as Meow>::Hey;
}

pub trait Foo {}

pub trait Bar {}

pub trait Baz {}

fn hello<T: Meow<Hey: Foo> + Meow<Hey: Bar>>(v: T) {
    demo(T::obtain(v));
}

fn demo<T: Foo + Bar + Baz>(v: T) {}
