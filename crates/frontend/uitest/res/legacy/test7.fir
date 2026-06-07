pub trait Meow {}

pub trait NeedsMeowAssoc {
    type T: Meow;
}

pub trait NeedsMeowGeneric<T: Meow> {}

pub trait Demo1 {
    type Foo;

    // This is accepted.
    type Bar: NeedsMeowAssoc<T = Foo>;
}

// This is accepted.
pub struct Demo2<Foo, Bar: NeedsMeowAssoc<T = Foo>>(Foo, Bar);

pub trait Demo3<T: Meow> {
    type Foo;

    // This is rejected.
    type Bar: NeedsMeowGeneric<<Self as Demo3<T>>::Foo>;
}

// This is rejected.
pub struct Demo4<Foo, Bar: NeedsMeowGeneric<Foo>>(Foo, Bar);

// Ignoring associated types is fine so long as our WF assumption on `impl`s holds.
impl NeedsMeowAssoc for () {
    // This is rejected.
    type T = ();
}
