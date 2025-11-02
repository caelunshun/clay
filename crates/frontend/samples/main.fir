pub trait Generic<T> {}

pub trait Associated {
    type T;
}

mod whee {
    use super::*;

    pub trait MyTrait<T: V22> {
        type V: Generic<T>;
    }
}
