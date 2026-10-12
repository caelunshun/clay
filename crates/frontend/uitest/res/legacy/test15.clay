pub trait Meow {}

impl Meow for () {}

pub trait Assoc {
    type Holder;
}

pub struct Miau1<T: Assoc<Holder = ()>>(Thump<<T as Assoc>::Holder>);

pub struct Miau2<T: Assoc<Holder = ((),)>>(Thump<<T as Assoc>::Holder>);

pub struct Thump<T: Meow>;
