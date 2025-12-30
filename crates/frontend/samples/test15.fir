pub trait Meow {}

impl Meow for () {}

pub trait Assoc {
    type Holder;
}

pub struct Miau<T: Assoc<Holder = ()>>(Thump<<T as Assoc>::Holder>);

pub struct Thump<T: Meow>;
