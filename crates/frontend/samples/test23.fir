struct Hello {}

impl Hello {
    fn meow() {}
}

struct Hi {}

impl Hi {
    fn meow() {}
}

fn main(foo: Hello, bar: Hi) {
    foo.meow;
    bar.meow;
}
