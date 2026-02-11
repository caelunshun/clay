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

    pub trait Haha {
        fn me<'a: &shorter Self>(me: &'a Self);
    }

    impl Haha for Hi {
        fn me<'a: &shorter Self>(me: &'a Self) {}
    }
}

use funky::Haha;

fn main(foo: Hello, bar: Hi) {
    (&foo).meow;
    (&bar).meow;
    (bar).meow;
    (&bar).hi;

    fn meow(foo: Hello) {
        kslfkj
    }
}
