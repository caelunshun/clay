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

pub trait Projector<T> {
    type Out;
}

fn hello<
    T: Projector<i32>
     + Projector<u32, Out = <T as Projector<i32>>::Out>
     + Meow<<T as Projector<i32>>::Out, Hey: Foo>
     + Meow<<T as Projector<u32>>::Out, Hey: Bar>
>(
    v: T,
) {
    demo::<<T as Meow<<T as Projector<i32>>::Out>>::Hey>(T::obtain(v));

    let v = T::obtain(v);
    demo::<_>(v);
    demo(v);
}

fn demo<T: Foo + Bar + Baz>(v: T) {}
