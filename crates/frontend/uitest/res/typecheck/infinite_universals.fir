#[lang("fn_once_trait")]
trait FnOnce<I, O> {}

trait Meow {
    type Generator: for<T> UhOh<T>;

    fn get_universal<T>() -> <Generator as UhOh<T>>::Output {
        loop {}
    }
}

trait UhOh<T> {
    type Output;
}

fn uhh<T: Meow>() {
    let foo = T::get_universal::<u32>();
    let bar = T::get_universal::<i32>();

    // FIXME: Should be rejected.
    // Idea: we can leave HRTB projections uninstantiated during elaboration and let the
    // `oblige_impl` routine contribute new instantiations of that HRTB just in front of it in the
    // elaborated clause list.
    eq(foo, bar);
}

fn eq<T>(lhs: T, rhs: T) {}
