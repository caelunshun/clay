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

trait Projector {
    type Out;
}

trait Helper<T> {
    fn meow(me: Self);
}

// We need to defer importing of HRTB `SigProject` and `SigAlias` types until the
// `HrtbSubstitutionFolder` is used.
fn uh_oh<Q: for<T: Projector> Helper<<T as Projector>::Out>>(v: Q) {
    Helper::<_>::meow(v);
}
