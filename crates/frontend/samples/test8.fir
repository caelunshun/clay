mod demo1 {
    pub trait Demo<'c> {
        type Foo: &longer 'c;
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
    impl<'a, 'b: &longer 'a> Demo<'a> for &'b () {
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
    impl<'b: &longer 'c, 'c: &longer 'b> Woo for ((&'b (), &'c ()), ()) {
        type Huh = (&'b (), &'c ());
    }

    // Rejected
    impl<'b: &longer 'c, 'c> Woo for ((&'b (), &'c ()), ((),)) {
        type Huh = (&'b (), &'c ());
    }

    // Rejected
    impl<'b, 'c> Woo for ((&'b (), &'c ()), (((),),)) {
        type Huh = (&'b (), &'c ());
    }
}
