#[lang("deref_trait")]
pub trait Deref {
    type Target;
}

pub enum Option<T> {
    Some(T),
    None,
}

pub use Option::*;

pub trait Iterator {
    type Item: for<'a: &shorter Self> IteratorItem<'a>;

    fn next<'a: &shorter Self>(this: &'a mut Self)
        -> Option<<<Self as Iterator>::Item as IteratorItem<'a>>::Out>;
}

pub trait IteratorItem<'a> {
    type Out: &longer 'a;
}

pub struct IteratorItemRef<T>;

impl<'a, T: &longer 'a> IteratorItem<'a> for IteratorItemRef<T> {
    type Out = &'a T;
}

pub struct IteratorItemMut<T>;

impl<'a, T: &longer 'a> IteratorItem<'a> for IteratorItemMut<T> {
    type Out = &'a mut T;
}

pub struct Forever<T> {
    pub elem: T,
}

impl<T> Iterator for Forever<T> {
    type Item = IteratorItemMut<T>;

    fn next<'a: &shorter Self>(this: &'a mut Self) -> Option<&'a mut T> {
        Some(&this.elem)
    }
}

pub trait Demo {
    fn demo();
}

fn main() {
    Demo::demo;
}
