mod part1 {
    pub trait Generic<T> {}

    impl<T> Generic<T> for T {}

    impl Generic<((),)> for () {}

    impl Generic<((),)> for (((),),) {}

    pub trait Spec {
        type Foo: Generic<Baz>;
        type Bar: Generic<Baz>;
        type Baz;
    }

    pub trait Demo {
        // How do we check WF if we don't know `Baz`?
        // Rust accepts this!
        type Whee: Spec<Foo = (), Bar = (((),),)>;

        // Rust accepts this too...?
        type Woo: Spec<Foo = (), Bar = ((((),),),)>;
    }
}

mod part2 {
    pub trait Generic<T> {}

    pub trait Spec {
        type Foo: Generic<Bar>;
        type Bar;
    }

    pub trait Demo {
        // Oh. Rust just ignores this too. Guess we have to defer WF checks until we know the
        // dependent generic parameters. Weird.
        type Meow: Spec<Foo = ()>;

        // But this should be properly rejected.
        type Thump: Spec<Foo = (), Bar = ()>;
    }
}
