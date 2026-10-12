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

trait Meow {}

struct Vec<T>;

impl<T> Vec<T> {
    fn new() -> Self {
        Self
    }

    fn push(&mut self, value: T) {}

    fn len(&self) -> u32 {
        loop {}
    }
}

fn accepted(meow: @dyn Meow) {
    let meow = meow.use;

    // Accepted because runtime knows type of `meow`.
    let mut foo = Vec::new();

    foo.push(meow);
}

fn rejected_simple(meow: @dyn Meow) {
    // FIXME: Reject because runtime does not yet know the type of `Meow`.
    let mut foo = Vec::new();

    let meow = meow.use;

    foo.push(meow);
}


fn rejected_complex(meow: @dyn Meow) {
    // FIXME: Reject because runtime does not yet know the type of `Meow`.
    let mut foo = Vec::new();

    _ = foo;
    let meow = meow.use;
    foo = Vec::new();

    foo.push(meow);
}
