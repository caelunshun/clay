pub enum Whee<T> {
    Foo(T, (T, T)),
    Bar,
    Baz {},
    Maz { foo: u32, bar: i32 },
}

pub struct Woo<'a, T> {
    pub foo: &'a T,
    bar: (),
}

pub struct Waz(pub u32, pub (), pub(crate) ());

pub struct Faz;

fn whee() -> Whee<u32> {
    // TODO
}
