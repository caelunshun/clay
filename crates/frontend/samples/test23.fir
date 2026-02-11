struct Hello {}

struct Hi {}

mod funky {
    use super::*;

    impl Hello {
        pub fn meow<'a: &shorter Self>(me: &'a Self) {}
    }

    impl Hi {
        pub fn meow<'a: &shorter Self>(me: &'a Self) {}

        pub fn meow(me: Self) {}
    }

    pub trait Haha<T> {
        type Assoc;

        fn me<'a: &shorter Self>(me: &'a Self);
    }

    impl<T> Haha<T> for Hi {
        type Assoc = ();

        fn me<'a: &shorter Self>(me: &'a Self, value: T) {}
    }
}

use funky::Haha;

fn main(foo: Hello, bar: Hi) {
    (&foo).meow;
    (&bar).meow;
    (bar).meow;
    (&foo).me;
    (&bar).me;

    fn meow(foo: Hey) {
        kslfkj
    }

    type Hey = Hello;
}
