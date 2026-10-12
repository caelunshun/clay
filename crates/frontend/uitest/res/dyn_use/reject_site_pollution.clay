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

trait Meow {
    type Assoc;

    fn get_assoc(&self) -> Assoc;
}

struct Foo;

impl Meow for Foo {
    type Assoc = ();

    fn get_assoc(&self) -> () {}
}

struct Bar;

impl Meow for Bar {
    type Assoc = u32;

    fn get_assoc(&self) -> u32 {
        1
    }
}

struct Vec<T>;

impl<T> Vec<T> {
    fn new() -> Self {
        Self
    }

    fn push(&mut self, value: T) {}
}

fn main() {
    let mut collector = Vec::new();
    let mut i = 0;

    loop {
        let init: @dyn Meow;

        if i == 0 {
            init = Foo;
        } else if i == 1 {
            init = Bar;
        } else {
            break;
        }

        // FIXME: Must be rejected!
        collector.push(init.use.get_assoc());

        i += 1;
    }
}
