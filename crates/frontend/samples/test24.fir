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

pub trait Meow<T> {
    type Hey;

    fn obtain(me: Self) -> <Self as Meow<T>>::Hey;
}

pub trait Foo {}

pub trait Bar {}

pub trait Baz {}

pub trait Projector {
    type Out;
}

fn hello<
    T: Projector
     + Meow<<T as Projector>::Out, Hey: Foo>
     + Meow<<T as Projector>::Out, Hey: Bar>
>(
    v: T,
) {
    demo::<<T as Meow<<T as Projector>::Out>>::Hey>(T::obtain(v));

    let v = T::obtain(v);
    demo::<_>(v);
    demo(v);
}

fn demo<T: Foo + Bar>(v: T) {}
