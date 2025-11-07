pub trait Generic<T> {}

impl<T, V: Associated<T = T>> Generic<(V,)> for () {}

impl<T, V: Associated<T = T>> Generic<(V,)> for ((),) {}

pub trait Associated {
    type T;
}

impl<T> Associated for T {
    type T = T;
}

pub trait MyTrait {}

impl<A: Generic<D>, B: Generic<D>, C: Associated<T = D>, D> MyTrait for (A, B, C) {}

pub trait Demo<T: MyTrait> {}

pub trait Dummy {}

impl<T: Demo<((), (((),),), ((),))>> Dummy for T {}
