pub trait Whee {}

impl Whee for () {}

impl Whee for ((),) {}

pub trait Woo {
    type T: Whee;
}

impl Woo for () {
    type T = _;
}
