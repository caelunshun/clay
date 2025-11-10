pub trait Demo<'a> {
    type Foo: 'a;
}

// Accepted
impl<'a> Demo<'a> for () {
    type Foo = ();
}

// Accepted
impl<'a> Demo<'a> for () {
    type Foo = &'a ();
}

// Rejected
impl<'a, 'b> Demo<'a> for &'b () {
    type Foo = &'b ();
}
