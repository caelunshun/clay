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
