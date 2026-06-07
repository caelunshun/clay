#[lang("deref_trait")]
pub trait Deref {
    type Target;
}

impl<'a, T: &longer 'a> Deref for &'a T {
    type Target = T;
}

impl<'a, T: &longer 'a> Deref for &'a mut T {
    type Target = T;
}

#[lang("fn_once_trait")]
pub trait FnOnce<I, O> {}

#[lang("fn_mut_trait")]
pub trait FnMut<I, O>: FnOnce<I, O> {}

#[lang("fn_trait")]
pub trait Fn<I, O>: FnMut<I, O> {}

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

pub struct IteratorItemMut<T>;

impl<'a, T: &longer 'a> IteratorItem<'a> for IteratorItemMut<T> {
    type Out = &'a mut T;
}

pub struct Forever<T> {
    elem: T,
}

impl<T> Forever<T> {
    pub fn new(elem: T) -> Self {
        Self { elem }
    }
}

impl<T> Iterator for Forever<T> {
    type Item = IteratorItemMut<T>;

    fn next<'a: &shorter Self>(this: &'a mut Self) -> Option<&'a mut T> {
        Some(&this.elem)
    }
}

fn main() {
    let mut foo = true;
    let bar = Forever::new(4).next();
    foo = bar;
}
