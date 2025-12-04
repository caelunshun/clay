fn main() {
    Meow;
    Whee::Foo;
    Whee::Bar;
    Whee::Baz;
    Foo;
    Bar;
    Baz;
}

pub struct Meow {}

pub enum Whee {
    Foo,
    Bar {},
    Baz(),
}

use Whee::*;
