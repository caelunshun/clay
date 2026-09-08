#[lang("fn_once_trait")]
trait FnOnce<I, O> {}

type FunkyIdentity<T> = <(T,) as FunkyIdentityHelper>::Out;

trait FunkyIdentityHelper {
    type Out;
}

impl<T> FunkyIdentityHelper for (T,) {
    type Out = T;
}

trait Meow {
    type Generator: for<'a, T> UhOh<'a, FunkyIdentity<T>>;

    fn get_universal<'a, T>() -> <Generator as UhOh<'a, T>>::Output {
        loop {}
    }
}

trait UhOh<'a, T> {
    type Output;
}

struct AssertEq<T: IsEq>();

trait IsEq {}

impl<T> IsEq for (T, T) {}

struct Uhh<'a, 'b, T: Meow> {
    // Should be rejected.
    case1: AssertEq<(
        <<T as Meow>::Generator as UhOh<'a, u32>>::Output,
        <<T as Meow>::Generator as UhOh<'a, i32>>::Output,
    )>,
    // Should be rejected.
    case2: AssertEq<(
        <<T as Meow>::Generator as UhOh<'a, u32>>::Output,
        <<T as Meow>::Generator as UhOh<'b, u32>>::Output,
    )>,
    // Should be accepted.
    case3: AssertEq<(
        <<T as Meow>::Generator as UhOh<'a, u32>>::Output,
        <<T as Meow>::Generator as UhOh<'a, u32>>::Output,
    )>,
}

/*
fn uhh<'a, 'b, T: Meow>() {
    // FIXME: Should be rejected.
    eq(T::get_universal::<'a, u32>(), T::get_universal::<'a, i32>());

    // FIXME: Should be rejected.
    eq(T::get_universal::<'a, u32>(), T::get_universal::<'b, u32>());

    // Should be accepted.
    eq(T::get_universal::<'a, u32>(), T::get_universal::<'a, u32>());
}

fn eq<T>(lhs: T, rhs: T) {}
*/
