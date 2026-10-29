use crate::utils::lang::Extension;
use std::range::Range;

pub trait RangeExt: Extension<Range<Self::Idx>> {
    type Idx;

    fn map<V>(self, f: impl FnMut(Self::Idx) -> V) -> Range<V>;
}

impl<T> RangeExt for Range<T> {
    type Idx = T;

    fn map<V>(self, mut f: impl FnMut(Self::Idx) -> V) -> Range<V> {
        (f(self.start)..f(self.end)).into()
    }
}

pub trait NewtypedRangeExt: Extension<Range<Self::Idx>> {
    type Idx: index_vec::Idx;

    fn iter_newtyped(self) -> impl ExactSizeIterator<Item = Self::Idx> + DoubleEndedIterator;
}

impl<T: index_vec::Idx> NewtypedRangeExt for Range<T> {
    type Idx = T;

    fn iter_newtyped(self) -> impl ExactSizeIterator<Item = Self::Idx> + DoubleEndedIterator {
        self.map(T::index).into_iter().map(T::from_usize)
    }
}
