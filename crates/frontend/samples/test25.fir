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
    type Out;
}

impl Meow for () {
    type Out = ();
}

fn obtain<M: Meow>(me: M) -> <M as Meow>::Out {
    loop {}
}

fn hehe1<T: Meow<Out = u32>>(v: T) {
    let v: i32 = obtain(v);
}

fn hehe2<T: Meow>(v: T) {
    let v: i32 = obtain(v);
}

fn hehe3<T: Meow<Out = <T as Meow>::Out>>(v: T) {
    let v: i32 = obtain(v);
}
