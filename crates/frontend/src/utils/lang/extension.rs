mod sealed {
    pub trait Sealed<T: ?Sized> {}

    impl<T: ?Sized> Sealed<T> for T {}
}

pub trait Extension<T: ?Sized>: sealed::Sealed<T> {}

impl<T: ?Sized> Extension<T> for T {}
