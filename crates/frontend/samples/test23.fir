pub trait Meow {
    type Haha;

    fn nyo();
}

impl Meow for () {
    type Haha = ();

    fn nyo();
}

impl () {
    type H;
    type E = ();
}
