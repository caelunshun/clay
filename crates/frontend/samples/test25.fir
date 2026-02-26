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

pub trait Meow {}

impl Meow for () {}

fn demo() {
    hehe(1);
    hehe::<((),)>;
    hehe(((),));
}

fn hehe<T: Meow>(v: T) {}
