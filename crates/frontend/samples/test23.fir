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

    #[lang("into_iterator_trait")]
    pub trait IntoIterator {
        type IntoIter: Iterator<Item = Item>;
        type Item;
    }

    impl<I: Iterator> IntoIterator for I {
        type IntoIter = I;
        type Item = <I as Iterator>::Item;
    }

    #[lang("iterator_trait")]
    pub trait Iterator {
        type Item;
    }

    #[lang("fn_once_trait")]
    pub trait FnOnce<I, O> {}

    #[lang("fn_mut_trait")]
    pub trait FnMut<I, O>: FnOnce<I, O> {}

    #[lang("fn_trait")]
    pub trait Fn<I, O>: FnMut<I, O> {}

    #[lang("index_trait")]
    pub trait Index<I> {
        type Output: &longer Self;
    }

    pub trait Clone {
        fn clone<'a: &shorter Self>(me: &'a Self) -> Self;
    }
}

use std::Clone;

pub struct Vec<T> {
    my_field: (),
}

impl<T> Vec<T> {
    pub fn new() -> Self {
        todo()
    }

    pub fn push<'a: &shorter Self>(me: &'a mut Self, value: T) {
        todo()
    }

    pub fn clear<'a: &shorter Self>(me: &'a mut Self) {
        todo()
    }

    pub fn get<'a: &shorter Self>(me: &'a Self, idx: u32) -> &'a T {
        todo()
    }
}

impl<T> std::Index<u32> for Vec<T> {
    type Output = T;
}

impl<T: Clone> Clone for Vec<T> {
    fn clone<'a: &shorter Self>(me: &'a Self) -> Self {
        todo()
    }
}

impl<'a: &shorter T, T> std::Iterator for &'a Vec<T> {
    type Item = &'a T;
}

impl Clone for () {
    fn clone<'a: &shorter Self>(me: &'a Self) -> Self {
        todo()
    }
}

fn make_vec<T>() -> Vec<T> {
    todo()
}

fn todo() -> Never {
    loop {}
}

fn main() {
    let vec = ().make::<_>();

    vec.push(vec.my_field);
    let elem = vec[1];
    vec.push(elem.clone());

    let vec2 = Clone::clone(&vec);
    vec2.push(());

    for v in &vec2 {
        let _: &() = v;
    }
}

pub trait MakeVec {
    fn make<T>(me: Self) -> Vec<T>;
}

impl MakeVec for () {
    fn make<T>(me: Self) -> Vec<T> {
        todo();
    }
}

fn fail_1() {
    fn meow() {}

    meow
}

fn fail_2() {
    let mut v = ();

    let a = 'b: {
        if true {
            break 'b &v;
        }

        if true {
            break 'b &mut v;
        }

        todo()
    };

    let b = 'b: {
        if true {
            break 'b &mut v;
        }

        if true {
            break 'b &v;
        }

        todo()
    };

    let c: &() = 'b: {
        if true {
            break 'b &mut v;
        }

        if true {
            break 'b &v;
        }

        todo()
    };

    *&1 + -1
}
