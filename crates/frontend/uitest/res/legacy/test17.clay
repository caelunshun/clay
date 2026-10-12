pub trait Foo<A> {}

pub trait Bar<B>: for<T> Foo<T> {}

pub trait Meow {}

impl<C> Foo<C> for () {}

impl<D: Meow> Bar<D> for () {}
