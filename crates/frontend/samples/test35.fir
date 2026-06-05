/*
import(mode=report, ty=v)  // <-- succeeded
import(mode=delay_bug, ty=v)  // never fail

// Is it possible???
import(mode=report, ty=v)  // <--- succeeds
    ...
        ...
            import(mode=delay_bug, ty=v)  // <--- fails
*/

pub trait Meow<T> {
    type Out;
}

pub trait Bnuuy {
    type Out;
}

impl<T: Bnuuy<Out: Meow<T>>> Meow<T> for () {
    type Out = <<T as Bnuuy>::Out as Meow<T>>::Out;
}

fn hehe<B: Bnuuy<Out: Meow<B>>>(v: <() as Meow<B>>::Out) {

}
