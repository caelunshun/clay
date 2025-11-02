pub trait Generic<T> {}

pub trait Associated {
    type T;
}

pub trait MyTrait<T: V> {
    type V: Generic<T>;
}
