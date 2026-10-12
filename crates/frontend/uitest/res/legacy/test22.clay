pub type Mew<'a: &shorter T, T> = &'a T;

pub type Recursive = Recursive;

pub type MutuallyRecursive2 = MutuallyRecursive1;
pub type MutuallyRecursive1 = MutuallyRecursive2;

pub struct Meow<T: &longer 'gc> {
    foo: Mew<'gc, T>,
    bar: Recursive,
    baz: MutuallyRecursive1,
}
