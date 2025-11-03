pub trait Generic<T> {}

pub trait Associated {
    type T;
}

pub trait SubTrait: Associated<T = (T,)> {
    type T: Associated;
}
