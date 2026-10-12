#[lang("fn_once_trait")]
pub trait FnOnce<I, O> {}

mod pip {
    pub struct Meow(pub i32, u32);
}

use pip::Meow;

fn main() {
    let x = &mut 0;
    (*x,) = (0,);
    (foo(),) = (0,);

    let a;
    Meow(a, ..) = Meow(1, 1);
    Meow(a, _) = Meow(1, 1);

    struct Mew { a: i32, b: u32 }

    Mew { a, .. } = Mew { a: 1, b: 0 };
    Mew { a, b: _ } = Mew { a: 1, b: 0 };
    Mew { a } = Mew { a: 1, b: 0 };
}

fn foo() -> i32 {
    1
}
