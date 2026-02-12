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

    pub trait Hehe {
        fn meow(me: Self);
    }

    impl<T> Hehe for T {
        fn meow(me: Self) {}
    }

    pub trait Haha {
        fn meow(me: Self);
    }

    impl<T> Haha for T {
        fn meow(me: Self) {}
    }
}

use std::*;

struct Miau {}

impl Miau {
    fn meow(me: Self, v: ()) {}
}

fn demo(v: Miau) {
    v.meow(());
    ().meow();
}
