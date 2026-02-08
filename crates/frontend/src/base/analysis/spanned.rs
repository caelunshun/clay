use crate::{
    base::{
        Session,
        arena::{HasListInterner, Intern},
        syntax::Span,
    },
    utils::lang::IterEither,
};
use std::{array, fmt, hash, iter};

#[derive(Copy, Clone)]
pub struct Spanned<T> {
    pub value: T,
    pub span_info: SpannedInfo,
}

impl<T: fmt::Debug> fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
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

    pub fn new_saturated(value: T, span: Span, cx: &impl HasListInterner<SpannedInfo>) -> Self {
        Self {
            value,
            span_info: SpannedInfo::Tracked(span, cx.intern_list(&[])),
        }
    }

    pub fn new_maybe_saturated(
        value: T,
        span: Option<Span>,
        cx: &impl HasListInterner<SpannedInfo>,
    ) -> Self {
        if let Some(span) = span {
            Self::new_saturated(value, span, cx)
        } else {
            Self::new_unspanned(value)
        }
    }

    pub fn own_span_if_specified(&self) -> Option<Span> {
        self.span_info.own_span()
    }

    pub fn own_span(&self) -> Span {
        self.own_span_if_specified().unwrap_or(Span::DUMMY)
    }

    pub fn new_view<C>(
        own_span: Span,
        view: impl SpannedViewEncode<C, Unspanned = T>,
        cx: &C,
    ) -> Self {
        view.encode(own_span, cx)
    }

    pub fn view<C>(&self, cx: &C) -> T::View
    where
        T: SpannedViewDecode<C>,
    {
        T::decode(&self.value, self.span_info, cx)
    }
}

impl<T: Clone> Spanned<Intern<[T]>> {
    pub fn alloc_list(
        own_span: Span,
        elems: &[Spanned<T>],
        cx: &(impl HasListInterner<T> + HasListInterner<SpannedInfo>),
    ) -> Self
    where
        T: 'static + hash::Hash + Eq,
    {
        let span_info = cx.intern_list(&elems.iter().map(|v| v.span_info).collect::<Vec<_>>());
        let value = cx.intern_list(&elems.iter().map(|v| v.value.clone()).collect::<Vec<_>>());

        Self {
            value,
            span_info: SpannedInfo::Tracked(own_span, span_info),
        }
    }

    pub fn len(self, s: &Session) -> usize {
        self.value.r(s).len()
    }

    pub fn is_empty(self, s: &Session) -> bool {
        self.value.r(s).is_empty()
    }

    pub fn nth(self, at: usize, cx: &impl HasListInterner<SpannedInfo>) -> Spanned<T> {
        Spanned::new_raw(
            self.value.r(cx.session())[at].clone(),
            self.span_info.child_span_at(at, cx),
        )
    }

    pub fn iter(
        self,
        cx: &impl HasListInterner<SpannedInfo>,
    ) -> impl '_ + ExactSizeIterator<Item = Spanned<T>> {
        let values = self.value.r(cx.session());

        values
            .iter()
            .zip(self.span_info.child_span_iter(values.len(), cx))
            .map(|(value, span_info)| Spanned::new_raw(value.clone(), span_info))
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum SpannedInfo {
    Untracked,
    Tracked(Span, Intern<[SpannedInfo]>),
}

impl SpannedInfo {
    pub fn new_optional(info: Option<SpannedInfo>) -> Self {
        info.unwrap_or(SpannedInfo::Untracked)
    }

    pub fn new_list(
        own_span: Span,
        children: &[SpannedInfo],
        cx: &impl HasListInterner<SpannedInfo>,
    ) -> Self {
        Self::Tracked(own_span, cx.intern_list(children))
    }

    pub fn new_terminal(own_span: Span, cx: &impl HasListInterner<SpannedInfo>) -> Self {
        Self::new_list(own_span, &[], cx)
    }

    pub fn new_maybe_terminal(
        own_span: Option<Span>,
        cx: &impl HasListInterner<SpannedInfo>,
    ) -> Self {
        match own_span {
            Some(own_span) => Self::new_terminal(own_span, cx),
            None => Self::Untracked,
        }
    }

    pub fn own_span(self) -> Option<Span> {
        match self {
            SpannedInfo::Untracked => None,
            SpannedInfo::Tracked(span, _) => Some(span),
        }
    }

    pub fn child_spans<const N: usize>(
        self,
        cx: &impl HasListInterner<SpannedInfo>,
    ) -> [SpannedInfo; N] {
        match self {
            SpannedInfo::Untracked => [SpannedInfo::Untracked; N],
            SpannedInfo::Tracked(own_span, child_spans) => {
                let child_spans = child_spans.r(cx.session());

                if child_spans.is_empty() {
                    [SpannedInfo::Tracked(own_span, cx.intern_list(&[])); N]
                } else {
                    array::from_fn(|i| child_spans[i])
                }
            }
        }
    }

    pub fn child_span_at(self, n: usize, cx: &impl HasListInterner<SpannedInfo>) -> SpannedInfo {
        match self {
            SpannedInfo::Untracked => SpannedInfo::Untracked,
            SpannedInfo::Tracked(own_span, child_spans) => {
                let child_spans = child_spans.r(cx.session());

                if child_spans.is_empty() {
                    SpannedInfo::Tracked(own_span, cx.intern_list(&[]))
                } else {
                    child_spans[n]
                }
            }
        }
    }

    pub fn child_span_iter<'s>(
        self,
        len: usize,
        cx: &'s impl HasListInterner<SpannedInfo>,
    ) -> impl 's + Clone + ExactSizeIterator<Item = SpannedInfo> {
        match self {
            SpannedInfo::Untracked => IterEither::Left(iter::repeat_n(SpannedInfo::Untracked, len)),
            SpannedInfo::Tracked(own_span, child_spans) => {
                let child_spans = child_spans.r(cx.session());

                if child_spans.is_empty() {
                    IterEither::Left(iter::repeat_n(
                        SpannedInfo::Tracked(own_span, cx.intern_list(&[])),
                        len,
                    ))
                } else {
                    debug_assert_eq!(child_spans.len(), len);

                    IterEither::Right(child_spans.iter().copied())
                }
            }
        }
    }

    pub fn wrap(self, own_span: Span, cx: &impl HasListInterner<SpannedInfo>) -> Self {
        Self::new_list(own_span, &[self], cx)
    }

    pub fn unwrap(self, cx: &impl HasListInterner<SpannedInfo>) -> SpannedInfo {
        let [child] = self.child_spans(cx);
        child
    }
}

pub trait SpannedViewDecode<C>: Sized {
    type View: SpannedViewEncode<C, Unspanned = Self>;

    fn decode(value: &Self, span_info: SpannedInfo, cx: &C) -> Self::View;
}

pub trait SpannedViewEncode<C>: Sized {
    type Unspanned: SpannedViewDecode<C, View = Self>;

    fn encode(self, own_span: Span, cx: &C) -> Spanned<Self::Unspanned>;
}
