struct Hello {}

struct Hi {}

mod funky {
    use super::*;

    impl Hello {
        pub fn meow() {}
    }

    impl Hi {
        fn meow() {}
    }
}

fn main(foo: Hello, bar: Hi) {
    foo.meow;
    bar.meow;
}
