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
}

fn main(foo: Hello, bar: Hi) {
    (&foo).meow;
    (&bar).meow;
    (bar).meow;
}
