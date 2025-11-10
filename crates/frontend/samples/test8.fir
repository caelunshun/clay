pub trait Demo<'c> {
    type Foo: 'c;
}

// Accepted
impl<'a> Demo<'a> for () {
    type Foo = ();
}

// Accepted
impl<'a> Demo<'a> for () {
    type Foo = &'a ();
}

// Accepted
impl<'a, 'b: 'a> Demo<'a> for &'b () {
    type Foo = &'b ();
}

// Rejected
impl<'a, 'b> Demo<'a> for &'b () {
    type Foo = &'b ();
}
