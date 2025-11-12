// Currently, we're generating the obligation...
//
// ```
// {Self: Foo<Bar = {Bar: Foo<Bar = {Self: ...}>}>}: Foo<Bar = {Self: ...}>
// ```
//
// This is rejected because `{Bar: Foo<Bar = {Self: ...}>}` does not equal `{Self: ...}` and yet
// this should compile.
//
// I think we're lowering the RHS incorrectly.
//
// To begin considering the bug, let's use the simpler form...
//
// ```rust
// pub trait Foo<T: Foo<Self>> {}
// ```
//
// Let's assume the LHS is correct:
//
// ```
// {Self: Foo<Bar = {Bar: Foo<Bar = {Self: ...}>}>}
// ```
//
// In order for a `Self` to be a valid `Bar`, it has to implement `Foo<Bar = Self>`. However, I
// think we got `Self` inside the clause wrong because, ultimately, the clause is on `Bar`. I
// think the clause should actually read...
//
// ```
// {Self: Foo<Bar = {Bar: Foo<Bar = {Self: ...}>}>}: Foo<Bar = {Bar}>
// ```
//
// Ugh. `Self` types are super confusing.

mod demo1 {
    pub trait Foo {
        type Bar: Foo<Bar = Self>;
    }
}

mod demo2 {
    pub trait Foo<T: Foo<Self>> {}
}

mod demo3 {
    // This is rejected :)
    pub trait Foo {
        type Bar: Foo<Bar = (Self,)>;
    }
}
