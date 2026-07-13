#[lang("fn_once_trait")]
pub trait FnOnce<I, O> {}

trait Meow {
    type Assoc;
}

impl<T> Meow for (T,) {
    type Assoc = T;
}

struct Thump<T: Meow<Assoc = u32>>(T);

fn meow() {
    Thump((infer(),));
}

fn infer<T>() -> T {
    loop {}
}
