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
}

pub trait Forever<T> {
    type Out;
}

impl<T: Forever<T>> Forever<T> for () {
    type Out = <T as Forever<T>>::Out;
}

fn meow(v: <() as Forever<()>>::Out) {}

// oblige (): Forever<(), Out = ?0>
//     T => ?1
//     oblige ?1: Forever<?1>
//         ...
//     oblige ?0 = <?1 as Forever<?1>>::Out
//         oblige ?1: Forever<?1, Out = ?0>
//             ...
