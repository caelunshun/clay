pub trait Meow {
    type Haha;

    fn nyo() {
        let foo: () = 'a';
    }

    fn required();
}

impl Meow for () {
    type Haha = ();

    fn nyo() {}

    fn nyo() {}

    fn required() {}
}

impl () {
    type H;
    type E = ();

    pub fn nyo() {
        let foo: () = 'a';
    }
}
