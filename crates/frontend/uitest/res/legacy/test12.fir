pub struct Whee<'a, T> {
    pub foo: T,
    bar: Waz<'a, ()>,
    foo: (),
}

pub enum Woo {
    Foo { pub foo: (), foo: () },
    Bar,
    Foo((), pub (), ()),
}

pub use Woo::*;

pub enum Waz<'a, T> {
    Foo(Whee<'a, (T, &'a ())>),
    Kaz(Foo),
}

pub enum What {
    Huh(u32),
    Quois(Huh),
}

use What::Huh::does_not_exist;

use What::Huh::super as lolwut;
