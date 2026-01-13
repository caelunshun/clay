pub trait Iterator {
    type Output: for<'a: &shorter Self> LendingOutput<'a>;

    fn next<'a: &shorter Self>(&'a mut self) -> <Self::Output as LendingOutput<'a>>::Output;
}

pub trait LendingOutput<'a> {
    // Very weird lifetime. Should usually be `&longer 'a`.
    // Also try ``.
    type Output: &shorter 'a;
}

pub struct LendingOutputSimpleMut<T>;

impl<'a, T: &longer 'a> LendingOutput<'a> for LendingOutputSimpleMut<T> {
    // Valid because `'a == 'a`.
    type Output = &'a mut T;
}

pub struct Forever<T>(pub T);

impl<T> Iterator for Forever<T> {
    type Output: &shorter 'a;

    fn next<'a: &shorter Self>(&'a mut self) -> <Self::Output as LendingOutput<'a>>::Output {
        &mut self.0
    }
}

pub fn demo(mut iter: impl Iterator) {
    let elem = iter.next();
    _ = iter;
    _ = elem;
}
