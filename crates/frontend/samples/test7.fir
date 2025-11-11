// This should compile.
//
// It currently doesn't because WF doesn't substitute `Self` for an appropriate universal parameter.
//
// Indeed, if we add...
//
// ```
// impl<T> Foo for T {
//     type Bar_ = Self;
// }
// ```
//
// ...the checker will crash because `Self` appears in the LHS.

pub trait Foo {
    type Bar_: Bar<Foo_ = Self>;
}

pub trait Bar {
    type Foo_: Foo<Bar_ = Self>;
}

pub trait Baz {
    type Whee: Baz;
}

impl Baz for () {
    type Whee = Self;
}
