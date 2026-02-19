pub mod std {
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

    pub trait Clone {
        fn clone<'a: &shorter Self>(me: &'a Self) -> Self;
    }
}

use std::Clone;

pub struct Vec<T> {
    my_field: (),
}

impl<T> Vec<T> {
    pub fn new() -> Self {}

    pub fn push<'a: &shorter Self>(me: &'a mut Self, value: T) {}

    pub fn clear<'a: &shorter Self>(me: &'a mut Self) {}

    pub fn get<'a: &shorter Self>(me: &'a Self, idx: u32) -> &'a T {}
}

impl<T: Clone> Clone for Vec<T> {
    fn clone<'a: &shorter Self>(me: &'a Self) -> Self {}
}

impl Clone for () {
    fn clone<'a: &shorter Self>(me: &'a Self) -> Self {}
}

fn make_vec<T>() -> Vec<T> {}

fn main() {
    let vec = ().make::<_>();

    vec.push(vec.my_field);
    let elem = vec.get(0);
    vec.push(elem.clone());

    let vec2 = Clone::clone(&vec);
    vec2.push(());
}

pub trait MakeVec {
    fn make<T>(me: Self) -> Vec<T> {}
}

impl MakeVec for () {
    fn make<T>(me: Self) -> Vec<T> {}
}
