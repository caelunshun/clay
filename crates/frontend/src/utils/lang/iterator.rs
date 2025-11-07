#[derive(Clone)]
pub enum IterEither<L, R> {
    Left(L),
    Right(R),
}

impl<T, L, R> ExactSizeIterator for IterEither<L, R>
where
    L: ExactSizeIterator<Item = T>,
    R: ExactSizeIterator<Item = T>,
{
}

impl<T, L, R> Iterator for IterEither<L, R>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            IterEither::Left(v) => v.next(),
            IterEither::Right(v) => v.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            IterEither::Left(v) => v.size_hint(),
            IterEither::Right(v) => v.size_hint(),
        }
    }
}
