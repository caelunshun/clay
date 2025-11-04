pub trait Generic<T> {}

impl<T> Generic<T> for T {}

impl Generic<()> for ((),) {}

pub trait Associated {
    type T;
}

impl<T> Associated for T {
    type T = T;
}

pub trait SubTrait: Associated<T = (T,)> {
    type T: Associated;
}
