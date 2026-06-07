// rustc properly rejects this without an overflow.

pub trait Generic<T> {}

impl Generic<()> for () {}

impl Generic<((),)> for () {}

impl<T: Generic<V>, V> Generic<V> for (T, T) {}

pub trait Associated {
    type T;
}

impl<T> Associated for T {
    type T = T;
}

pub trait MyTrait {}

impl<A: Generic<D>, B: Generic<D>, C: Associated<T = D>, D> MyTrait for (A, B, C) {}

pub trait Whee {
    type Woo: MyTrait;
}

impl<T: Associated<T = V>, D: Generic<V>, V> Whee for (T, V, D) {
    type Woo = ((D, D), V, T);
}
