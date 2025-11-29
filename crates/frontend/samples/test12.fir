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

pub enum Waz<'a, T> {
    Foo(Whee<'a, (T, &'a ())>),
}
