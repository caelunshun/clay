mod demo1 {
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
}

mod demo2 {
    pub trait Whee {}

    impl<'a> Whee for (&'a (), &'a ()) {}

    pub trait Woo {
        type Huh: Whee;
    }

    // Accepted
    impl<'b: 'c, 'c: 'b> Woo for ((&'b (), &'c ()), ()) {
        type Huh = (&'b (), &'c ());
    }

    // Rejected
    impl<'b: 'c, 'c> Woo for ((&'b (), &'c ()), ((),)) {
        type Huh = (&'b (), &'c ());
    }

    // Rejected
    impl<'b, 'c> Woo for ((&'b (), &'c ()), (((),),)) {
        type Huh = (&'b (), &'c ());
    }
}
