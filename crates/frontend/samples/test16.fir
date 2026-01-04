pub trait Meow<'a> {}

impl<'a> Meow<'a> for () {}

struct Foo<T: for<'a> Meow<'a>>;

struct Bar(Foo<()>);
