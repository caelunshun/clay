use crate::{
    base::{
        Session,
        arena::{HasListInterner, Intern, Obj},
        syntax::Span,
    },
    utils::lang::IterEither,
};
use std::{array, hash, iter};

#[derive(Debug, Copy, Clone)]
pub struct Spanned<T> {
    pub value: T,
    pub span_info: SpannedInfo,
}

impl<T> Spanned<T> {
    pub fn new_raw(value: T, span_info: SpannedInfo) -> Self {
        Self { value, span_info }
    }

    pub fn new_unspanned(value: T) -> Self {
        Self {
            value,
            span_info: SpannedInfo::Untracked,
        }
    }

    pub fn own_span(&self) -> Option<Span> {
        self.span_info.own_span()
    }

    pub fn new_view<C>(own_span: Span, view: T::View, cx: &C) -> Self
    where
        T: SpannedView<C>,
    {
        T::encode(own_span, view, cx)
    }

    pub fn view<C>(&self, cx: &C) -> T::View
    where
        T: SpannedView<C>,
    {
        T::decode(&self.value, self.span_info, cx)
    }
}

impl<T: Clone> Spanned<Intern<[T]>> {
    pub fn alloc_list(own_span: Span, elems: &[Spanned<T>], cx: &impl HasListInterner<T>) -> Self
    where
        T: 'static + hash::Hash + Eq,
    {
        let s = cx.session();
        let span_info = Obj::new_iter(elems.iter().map(|v| v.span_info), s);
        let value = cx.intern(&elems.iter().map(|v| v.value.clone()).collect::<Vec<_>>());

        Self {
            value,
            span_info: SpannedInfo::Tracked(own_span, span_info),
        }
    }

    pub fn len(self, s: &Session) -> usize {
        self.value.r(s).len()
    }

    pub fn nth(self, at: usize, s: &Session) -> Spanned<T> {
        Spanned::new_raw(
            self.value.r(s)[at].clone(),
            self.span_info.child_span_at(at, s),
        )
    }

    pub fn iter(self, s: &Session) -> impl '_ + ExactSizeIterator<Item = Spanned<T>> {
        let values = self.value.r(s);

        values
            .iter()
            .zip(self.span_info.child_span_iter(values.len(), s))
            .map(|(value, span_info)| Spanned::new_raw(value.clone(), span_info))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum SpannedInfo {
    Untracked,
    Tracked(Span, Obj<[SpannedInfo]>),
}

impl SpannedInfo {
    pub fn new_list(own_span: Span, children: &[SpannedInfo], s: &Session) -> Self {
        Self::Tracked(own_span, Obj::new_slice(children, s))
    }

    pub fn new_terminal(own_span: Span, s: &Session) -> Self {
        Self::new_list(own_span, &[], s)
    }

    pub fn own_span(self) -> Option<Span> {
        match self {
            SpannedInfo::Untracked => None,
            SpannedInfo::Tracked(span, _) => Some(span),
        }
    }

    pub fn child_spans<const N: usize>(self, s: &Session) -> [SpannedInfo; N] {
        match self {
            SpannedInfo::Untracked => [SpannedInfo::Untracked; N],
            SpannedInfo::Tracked(_, spans) => array::from_fn(|i| spans.r(s)[i]),
        }
    }

    pub fn child_span_at(self, n: usize, s: &Session) -> SpannedInfo {
        match self {
            SpannedInfo::Untracked => SpannedInfo::Untracked,
            SpannedInfo::Tracked(_, spans) => spans.r(s)[n],
        }
    }

    pub fn child_span_iter<'s>(
        self,
        len: usize,
        s: &'s Session,
    ) -> impl 's + Clone + ExactSizeIterator<Item = SpannedInfo> {
        let spans = match self {
            SpannedInfo::Untracked => {
                return IterEither::Left(iter::repeat_n(SpannedInfo::Untracked, len));
            }
            SpannedInfo::Tracked(_, spans) => spans.r(s),
        };

        debug_assert_eq!(spans.len(), len);

        IterEither::Right(spans.iter().copied())
    }

    pub fn wrap(self, own_span: Span, s: &Session) -> Self {
        Self::new_list(own_span, &[self], s)
    }

    pub fn unwrap(self, s: &Session) -> SpannedInfo {
        let [child] = self.child_spans(s);
        child
    }
}

pub trait SpannedView<C>: Sized {
    type View;

    fn decode(value: &Self, span_info: SpannedInfo, cx: &C) -> Self::View;

    fn encode(own_span: Span, view: Self::View, cx: &C) -> Spanned<Self>;
}
