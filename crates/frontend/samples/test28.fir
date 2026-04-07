trait Meow<A> {
    type Assoc;
}

fn main<T: Meow<V>, V>() {
    let x: <T as Meow<V>>::Assoc;

    if false {
        x;
        x;
    }

    x;
}
