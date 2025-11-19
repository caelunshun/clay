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
