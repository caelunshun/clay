use super::{Span, Spanned, Symbol};
use crate::{
    base::{Diag, ErrorGuaranteed, HardDiag, LeafDiag},
    utils::lang::Extension,
};
use std::fmt::Write as _;

// === Parse Error === //

#[derive(Debug, Clone)]
#[must_use]
pub struct RecoveryRequired(pub ErrorGuaranteed);

pub type PResult<T> = Result<T, RecoveryRequired>;
pub type OptPResult<T> = PResult<Option<T>>;

pub trait OptPResultExt: Sized + Extension<OptPResult<Self::Value>> {
    type Value;

    fn did_match(self) -> Option<PResult<Self::Value>>;
}

impl<T> OptPResultExt for OptPResult<T> {
    type Value = T;

    fn did_match(self) -> Option<PResult<Self::Value>> {
        self.transpose()
    }
}

// === Parser Core === //

#[derive(Debug)]
pub struct Parser<I> {
    cursor: Cursor<I>,
    context: Vec<(Span, Symbol)>,
    expected: Vec<Symbol>,
    stuck_hints: Vec<LeafDiag>,
}

impl<I: CursorIter> Parser<I> {
    pub fn new(raw: impl Into<I>) -> Self {
        Self {
            cursor: Cursor::new(raw.into()),
            context: Vec::new(),
            expected: Vec::new(),
            stuck_hints: Vec::new(),
        }
    }

    pub fn enter(&self, sub: impl Into<I>) -> Self {
        Self::new(sub.into())
    }

    fn moved_forwards(&mut self) {
        self.expected.clear();
        self.stuck_hints.clear();
    }

    pub fn irrefutable<R>(&mut self, f: impl FnOnce(&mut Cursor<I>) -> R) -> R {
        self.moved_forwards();
        f(&mut self.cursor)
    }

    #[must_use]
    pub fn expect_covert_hinted<R>(
        &mut self,
        visible: bool,
        what: Symbol,
        f: impl FnOnce(&mut Cursor<I>, &mut StuckHinter<'_>) -> R,
    ) -> R
    where
        R: LookaheadResult,
    {
        let mut hinter = StuckHinter(Some(&mut self.stuck_hints));
        let res = self.cursor.lookahead(|c| f(c, &mut hinter));

        if res.is_ok() {
            self.moved_forwards();
        } else if visible {
            self.expected.push(what);
        }

        res
    }

    #[must_use]
    pub fn expect_covert<R>(
        &mut self,
        visible: bool,
        what: Symbol,
        f: impl FnOnce(&mut Cursor<I>) -> R,
    ) -> R
    where
        R: LookaheadResult,
    {
        self.expect_covert_hinted(visible, what, |c, _hinter| f(c))
    }

    #[must_use]
    pub fn expect_hinted<R>(
        &mut self,
        what: Symbol,
        f: impl FnOnce(&mut Cursor<I>, &mut StuckHinter<'_>) -> R,
    ) -> R
    where
        R: LookaheadResult,
    {
        self.expect_covert_hinted(true, what, f)
    }

    #[must_use]
    pub fn expect<R>(&mut self, what: Symbol, f: impl FnOnce(&mut Cursor<I>) -> R) -> R
    where
        R: LookaheadResult,
    {
        self.expect_covert_hinted(true, what, |c, _hinter| f(c))
    }

    pub fn next_span(&self) -> Span {
        self.cursor.next_span()
    }

    pub fn prev_span(&self) -> Span {
        self.cursor.prev_span()
    }

    pub fn context<R>(&mut self, what: Symbol, f: impl FnOnce(&mut Self) -> R) -> R {
        self.context.push((self.next_span(), what));
        let res = f(self);
        self.context.pop();
        res
    }

    pub fn hint_syntactic(&mut self, f: impl FnOnce(&mut Cursor<I>, &mut StuckHinter<'_>)) {
        f(
            &mut self.cursor.clone(),
            &mut StuckHinter(Some(&mut self.stuck_hints)),
        )
    }

    pub fn hint_if_passes<R>(
        &mut self,
        parse: impl FnOnce(&mut Cursor<I>, &mut StuckHinter<'_>) -> R,
        gen_diag: impl FnOnce(Span, R) -> LeafDiag,
    ) where
        R: LookaheadResult,
    {
        self.hint_syntactic(|c, hinter| {
            let start = c.next_span();
            let res = parse(c, hinter);
            if res.is_ok() {
                hinter.hint(gen_diag(start.to(c.prev_span()), res));
            }
        });
    }

    pub fn expect_or_hint<R>(
        &mut self,
        is_expected: bool,
        what: Symbol,
        parse: impl FnOnce(&mut Cursor<I>, &mut StuckHinter<'_>) -> R,
        gen_diag: impl FnOnce(Span, R) -> LeafDiag,
    ) -> R
    where
        R: LookaheadResult + DefaultReject,
    {
        if is_expected {
            self.expect_hinted(what, parse)
        } else {
            self.hint_if_passes(parse, gen_diag);
            R::default_reject()
        }
    }

    pub fn maybe_expect<R>(
        &mut self,
        is_expected: bool,
        what: Symbol,
        f: impl FnOnce(&mut Cursor<I>, &mut StuckHinter<'_>) -> R,
    ) -> R
    where
        R: LookaheadResult + DefaultReject,
    {
        if is_expected {
            self.expect_hinted(what, f)
        } else {
            R::default_reject()
        }
    }

    pub fn hint(&mut self, diag: LeafDiag) {
        self.stuck_hints.push(diag);
    }

    pub fn stuck(&mut self) -> RecoveryRequired {
        let mut msg = String::new();

        msg.push_str("expected ");

        msg.push_str(match self.expected.len() {
            0 => "nothing (this is likely a bug)",
            1..=2 => "",
            3.. => "one of ",
        });

        for (i, expectation) in self.expected.iter().copied().enumerate() {
            if i > 0 && self.expected.len() > 2 {
                msg.push(',');
            }

            if i == self.expected.len() - 1 && self.expected.len() > 1 {
                msg.push_str(" or");
            }

            if i > 0 {
                msg.push(' ');
            }

            write!(msg, "{expectation}").unwrap();
        }

        let mut diag = Diag::span_err(self.next_span(), msg);

        diag.children.extend_from_slice(&self.stuck_hints);

        if let Some(&(cx_span, cx_what)) = self.context.last() {
            diag.push_child(LeafDiag::span_once_note(
                cx_span,
                format_args!("this error ocurred while {cx_what}"),
            ));
        }

        self.moved_forwards();

        RecoveryRequired(diag.emit())
    }

    #[must_use]
    pub fn stuck_recover(&mut self) -> &mut Cursor<I> {
        let err = self.stuck();
        self.recover(err)
    }

    pub fn stuck_recover_with(&mut self, f: impl FnOnce(&mut Cursor<I>)) -> ErrorGuaranteed {
        let err = self.stuck();
        self.recover_with(err, f)
    }

    #[must_use]
    pub fn recover(&mut self, err: RecoveryRequired) -> &mut Cursor<I> {
        let _ = err;
        self.moved_forwards();

        &mut self.cursor
    }

    pub fn recover_with(
        &mut self,
        err: RecoveryRequired,
        f: impl FnOnce(&mut Cursor<I>),
    ) -> ErrorGuaranteed {
        let err_guar = err.0;

        f(self.recover(err));

        err_guar
    }

    pub fn err(&self, diag: HardDiag) -> RecoveryRequired {
        RecoveryRequired(diag.emit())
    }

    pub fn cursor_unsafe(&self) -> &Cursor<I> {
        &self.cursor
    }

    pub fn cursor_unsafe_mut(&mut self) -> &mut Cursor<I> {
        &mut self.cursor
    }
}

#[derive(Debug)]
pub struct StuckHinter<'a>(pub Option<&'a mut Vec<LeafDiag>>);

impl StuckHinter<'_> {
    pub const fn new_dummy() -> Self {
        Self(None)
    }

    pub fn hint(&mut self, diag: LeafDiag) -> &mut Self {
        if let Some(inner) = &mut self.0 {
            inner.push(diag);
        }

        self
    }
}

pub trait Matcher<I: CursorIter> {
    type Handler: Fn(&mut Cursor<I>, &mut StuckHinter<'_>) -> Self::Output;
    type Output: LookaheadResult;

    fn expectation(&self) -> Symbol;

    fn matcher(&self) -> &Self::Handler;

    fn consume(&self, c: &mut Cursor<I>) -> Self::Output {
        c.lookahead(|c| self.matcher()(c, &mut StuckHinter::new_dummy()))
    }

    fn did_consume(&self, c: &mut Cursor<I>) -> bool {
        self.consume(c).is_ok()
    }

    fn expect(&self, p: &mut Parser<I>) -> Self::Output {
        p.expect_hinted(self.expectation(), self.matcher())
    }

    fn expect_covert(&self, visible: bool, p: &mut Parser<I>) -> Self::Output {
        p.expect_covert_hinted(visible, self.expectation(), self.matcher())
    }

    fn hint_if_match(
        &self,
        p: &mut Parser<I>,
        gen_diag: impl FnOnce(Span, Self::Output) -> LeafDiag,
    ) {
        p.hint_if_passes(self.matcher(), gen_diag);
    }

    fn expect_or_hint(
        &mut self,
        p: &mut Parser<I>,
        is_expected: bool,
        gen_diag: impl FnOnce(Span, Self::Output) -> LeafDiag,
    ) -> Self::Output
    where
        Self::Output: DefaultReject,
    {
        p.expect_or_hint(is_expected, self.expectation(), self.matcher(), gen_diag)
    }

    fn maybe_expect(&mut self, p: &mut Parser<I>, is_expected: bool) -> Self::Output
    where
        Self::Output: DefaultReject,
    {
        p.maybe_expect(is_expected, self.expectation(), self.matcher())
    }
}

impl<C, F, O> Matcher<C> for (Symbol, F)
where
    F: Fn(&mut Cursor<C>, &mut StuckHinter<'_>) -> O,
    O: LookaheadResult,
    C: CursorIter,
{
    type Handler = F;
    type Output = O;

    fn expectation(&self) -> Symbol {
        self.0
    }

    fn matcher(&self) -> &Self::Handler {
        &self.1
    }
}

#[derive(Debug, Clone)]
pub struct Cursor<I> {
    pub iter: I,
    pub prev_span: Span,
}

impl<I: CursorIter> Cursor<I> {
    pub fn new(raw: I) -> Self {
        Self {
            prev_span: raw.start_span(),
            iter: raw,
        }
    }

    pub fn eat_full(&mut self) -> I::Item {
        let next = self.iter.next().unwrap();
        self.prev_span = next.span();
        next
    }

    pub fn peek_full(&self) -> I::Item {
        self.iter.clone().next().unwrap()
    }

    pub fn eat(&mut self) -> I::Simplified {
        self.eat_full().simplify()
    }

    pub fn peek(&self) -> I::Simplified {
        self.peek_full().simplify()
    }

    pub fn next_span(&self) -> Span {
        self.peek_full().span()
    }

    pub fn prev_span(&self) -> Span {
        self.prev_span
    }

    pub fn lookahead<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R
    where
        R: LookaheadResult,
    {
        let mut fork = self.clone();
        let res = f(&mut fork);
        if res.is_ok() {
            *self = fork;
        }

        res
    }
}

// === Traits === //

pub trait LookaheadResult {
    fn is_ok(&self) -> bool;
}

impl LookaheadResult for bool {
    fn is_ok(&self) -> bool {
        *self
    }
}

impl<T> LookaheadResult for Option<T> {
    fn is_ok(&self) -> bool {
        self.is_some()
    }
}

impl<T, E> LookaheadResult for Result<T, E> {
    fn is_ok(&self) -> bool {
        self.is_ok()
    }
}

pub trait DefaultReject: LookaheadResult {
    fn default_reject() -> Self;
}

impl DefaultReject for bool {
    fn default_reject() -> Self {
        false
    }
}

impl<T> DefaultReject for Option<T> {
    fn default_reject() -> Self {
        None
    }
}

impl<T, E: Default> DefaultReject for Result<T, E> {
    fn default_reject() -> Self {
        Err(E::default())
    }
}

pub trait AtomSimplify {
    type Simplified;

    fn simplify(self) -> Self::Simplified;
}

pub trait Delimited {
    fn start_span(&self) -> Span;

    fn end_span(&self) -> Span;
}

pub trait CursorIter:
    Sized + Iterator<Item: AtomSimplify<Simplified = Self::Simplified> + Spanned> + Clone + Delimited
{
    type Simplified;
}

impl<I, A, S> CursorIter for I
where
    I: Clone + Iterator<Item = A> + Delimited,
    A: AtomSimplify<Simplified = S> + Spanned,
{
    type Simplified = S;
}

// === Standard Cursors === //

pub type CharParser<'ch> = Parser<RawCharCursor<'ch>>;
pub type CharCursor<'ch> = Cursor<RawCharCursor<'ch>>;

#[derive(Debug, Clone)]
pub struct RawCharCursor<'a> {
    span: Span,
    iter: std::str::CharIndices<'a>,
}

impl<'a> RawCharCursor<'a> {
    pub fn new(span: Span, contents: &'a str) -> Self {
        Self {
            span,
            iter: contents.char_indices(),
        }
    }

    pub fn remaining_text(&self) -> &'a str {
        self.iter.as_str()
    }
}

impl Delimited for RawCharCursor<'_> {
    fn start_span(&self) -> Span {
        self.span.shrink_to_lo()
    }

    fn end_span(&self) -> Span {
        self.span.shrink_to_hi()
    }
}

impl Iterator for RawCharCursor<'_> {
    type Item = SpannedChar;

    fn next(&mut self) -> Option<Self::Item> {
        let Some((pos, ch)) = self.iter.next() else {
            return Some(SpannedChar {
                ch: None,
                span: self.end_span(),
            });
        };

        Some(SpannedChar {
            ch: Some(ch),
            span: Span::new_sized(self.span.lo + pos, ch.len_utf8()),
        })
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SpannedChar {
    pub ch: Option<char>,
    pub span: Span,
}

impl AtomSimplify for SpannedChar {
    type Simplified = Option<char>;

    fn simplify(self) -> Self::Simplified {
        self.ch
    }
}

impl Spanned for SpannedChar {
    fn span(&self) -> Span {
        self.span
    }
}

pub trait SpanCharMatcher: for<'a> Matcher<RawCharCursor<'a>> {}

impl<T> SpanCharMatcher for T where T: for<'a> Matcher<RawCharCursor<'a>> {}

pub fn span_char_matcher<F, R>(name: Symbol, matcher: F) -> (Symbol, F)
where
    F: Fn(&mut Cursor<RawCharCursor>, &mut StuckHinter<'_>) -> R,
    R: LookaheadResult,
{
    (name, matcher)
}
