pub type Mew<'a: &shorter T, T> = &'a T;

pub struct Meow<T: &longer 'gc> {
    foo: Mew<'gc, T>,
}
