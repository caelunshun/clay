/*
pub trait Generic<T> {}

impl<T> Generic<T> for T {}

impl Generic<i32> for u32 {}

pub trait Associated {
    type T;
}

impl<V> Associated for V {
    type T = V;
}

pub trait MyTrait<T> {}

impl<Q: Generic<T>, R: Associated<T = T>, S, T> MyTrait<()> for (Q, R, S) {}
*/

trait Whee<A, B, C>
