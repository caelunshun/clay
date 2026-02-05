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

struct Foo;

struct Bar;

impl Deref for Bar {
    type Target = Foo;
}

struct Baz;

impl Deref for Baz {
    type Target = Foo;
}

fn demo() {
    let a: Bar;
    let b: Baz;

    let foo = if true {
        &a
    } else {
        &b
    };
}
