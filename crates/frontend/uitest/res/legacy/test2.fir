pub trait Generic<T> {}

// Swap which impl is uncommented for a mind-boggling effect.
impl<T: Generic<V>, V> Generic<V> for T {}
// impl<V, T: Generic<V>> Generic<V> for T {}

pub trait Demo {
    type Foo;
    type Bar: Generic<Foo>;
}

impl<A, B> Demo for (A, B) {
    type Foo = A;
    type Bar = B;
}
