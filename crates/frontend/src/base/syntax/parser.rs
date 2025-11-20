use super::{HasSpan, Span, Symbol};
use crate::{
    base::{Diag, ErrorGuaranteed, HardDiag, LeafDiag},
    utils::{
        hash::FxIndexMap,
        lang::{FormatFn, ListFormatter, OR_LIST_GLUE, format_list_into},
    },
};
use std::fmt::Debug;

// === Parser Core === //

#[derive(Debug)]
pub struct Parser<I> {
    /// The raw cursor to the stream we're parsing.
    cursor: Cursor<I>,

    /// The set of items we could expect at a given position.
    expected: Vec<Expectation>,

    /// The set of hint diagnostics to emit if we get stuck on the current parse element.
    stuck_hints: Vec<LeafDiag>,

    /// What we would parse if we met an expectation specified in a block with this set.
    ///
    /// The `u64` represents the position of the cursor at which this expectation would be a
    /// `Starting` expectation. All other positions (especially `u64::MAX`) would lead to a
    /// `Continuing` expectation.
    to_parse: Option<(Symbol, u64)>,

    /// Whether we've encountered an error that still needs to recovered from by realigning the
    /// parser with a sensible portion of the input stream.
    needs_recovery: bool,
}

#[derive(Debug, Copy, Clone)]
struct Expectation {
    what: Symbol,
    to_parse: Option<(Symbol, ToParseMode)>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ToParseMode {
    Starting,
    Continuing,
}

impl<I: CursorIter> Parser<I> {
    pub fn new(raw: impl Into<I>) -> Self {
        Self {
            cursor: Cursor::new(raw.into()),
            to_parse: None,
            expected: Vec::new(),
            stuck_hints: Vec::new(),
            needs_recovery: false,
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
        self.recover_chomp();
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
        self.recover_chomp();

        let mut hinter = StuckHinter(Some(&mut self.stuck_hints));
        let res = self.cursor.lookahead(|c| f(c, &mut hinter));

        if res.is_ok() {
            self.moved_forwards();
        } else if visible {
            self.expected.push(Expectation {
                what,
                to_parse: self.to_parse.map(|(what, start_if_at_position)| {
                    let mode = if self.cursor.position == start_if_at_position {
                        ToParseMode::Starting
                    } else {
                        ToParseMode::Continuing
                    };

                    (what, mode)
                }),
            });
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

    pub fn next_span_not_eos(&self) -> Option<Span> {
        self.cursor.next_span_not_eos()
    }

    pub fn prev_span(&self) -> Span {
        self.cursor.prev_span()
    }

    pub fn to_parse<R>(
        &mut self,
        what: Symbol,
        mode: ToParseMode,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let start_if_at_pos = match mode {
            ToParseMode::Starting => self.cursor.position,
            ToParseMode::Continuing => u64::MAX,
        };

        let old = self.to_parse.replace((what, start_if_at_pos));
        let res = f(self);
        self.to_parse = old;
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

    pub fn stuck(&mut self) -> ErrorGuaranteed {
        self.needs_recovery = true;

        let mut msg = String::new();

        msg.push_str("expected ");

        if self.expected.is_empty() {
            msg.push_str("nothing (this is likely a bug)");
        }

        let mut to_start_expectations = FxIndexMap::<Symbol, Vec<Symbol>>::default();
        let mut to_continue_expectations = FxIndexMap::<Symbol, Vec<Symbol>>::default();
        let mut basic_expectations = Vec::new();

        for &Expectation { what, to_parse } in self.expected.iter() {
            match to_parse {
                Some((category, mode)) => {
                    let map = match mode {
                        ToParseMode::Starting => &mut to_start_expectations,
                        ToParseMode::Continuing => &mut to_continue_expectations,
                    };

                    map.entry(category).or_default().push(what);
                }
                None => {
                    basic_expectations.push(what);
                }
            }
        }

        let mut list_fmt = ListFormatter::default();

        for (sub_list_prefix, sub_list) in [
            ("start of ", &to_start_expectations),
            ("next part of ", &to_continue_expectations),
        ] {
            if sub_list.is_empty() {
                continue;
            }

            let sub_list_fmt = FormatFn(|f| {
                f.write_str(sub_list_prefix)?;

                let mut list_fmt = ListFormatter::default();

                for (&to_parse, whats) in sub_list {
                    list_fmt
                        .push(
                            f,
                            FormatFn(|f| {
                                write!(f, "{to_parse}")?;
                                f.write_str(" (")?;
                                format_list_into(f, whats, OR_LIST_GLUE)?;
                                f.write_str(")")?;

                                Ok(())
                            }),
                            OR_LIST_GLUE,
                        )
                        .unwrap();
                }

                list_fmt.finish(f, OR_LIST_GLUE)
            });

            list_fmt.push(&mut msg, sub_list_fmt, OR_LIST_GLUE).unwrap();
        }

        list_fmt
            .push_many(&mut msg, basic_expectations, OR_LIST_GLUE)
            .unwrap();

        list_fmt.finish(&mut msg, OR_LIST_GLUE).unwrap();

        let mut diag = Diag::span_err(
            self.next_span_not_eos()
                .unwrap_or(self.prev_span().shrink_to_hi()),
            msg,
        );
        diag.children.extend_from_slice(&self.stuck_hints);

        self.moved_forwards();

        diag.emit()
    }

    pub fn err(&mut self, diag: HardDiag) -> ErrorGuaranteed {
        self.needs_recovery = true;

        diag.emit()
    }

    pub fn recover(&mut self, f: impl FnOnce(&mut Cursor<I>)) {
        if !self.needs_recovery {
            return;
        }

        self.needs_recovery = false;
        f(&mut self.cursor);
    }

    pub fn recover_until<R: LookaheadResult>(&mut self, f: impl FnMut(&mut Cursor<I>) -> R) {
        self.recover(|c| {
            c.eat_until(f);
        });
    }

    pub fn recover_chomp(&mut self) {
        self.recover(|c| {
            c.eat();
        });
    }

    pub fn stuck_immediate_recover(&mut self, f: impl FnOnce(&mut Cursor<I>)) -> ErrorGuaranteed {
        let err = self.stuck();
        self.recover(f);
        err
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
    pub position: u64,
}

impl<I: CursorIter> Cursor<I> {
    pub fn new(raw: I) -> Self {
        Self {
            prev_span: raw.start_span(),
            iter: raw,
            position: 0,
        }
    }

    pub fn eat_full(&mut self) -> I::Item {
        let next = self.iter.next().unwrap();
        self.position += 1;
        if !next.is_eos() {
            self.prev_span = next.span();
        }
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

    pub fn next_span_not_eos(&self) -> Option<Span> {
        (!self.peek_full().is_eos()).then(|| self.next_span())
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

    pub fn eat_until<R>(&mut self, mut f: impl FnMut(&mut Self) -> R) -> R
    where
        R: LookaheadResult,
    {
        loop {
            let res = self.lookahead(&mut f);

            if res.is_ok() {
                break res;
            }

            self.eat();
        }
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

    fn is_eos(&self) -> bool;
}

pub trait Delimited {
    fn start_span(&self) -> Span;

    fn end_span(&self) -> Span;
}

pub trait CursorIter:
    Sized + Iterator<Item: AtomSimplify<Simplified = Self::Simplified> + HasSpan> + Clone + Delimited
{
    type Simplified;
}

impl<I, A, S> CursorIter for I
where
    I: Clone + Iterator<Item = A> + Delimited,
    A: AtomSimplify<Simplified = S> + HasSpan,
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

    fn is_eos(&self) -> bool {
        self.ch.is_none()
    }
}

impl HasSpan for SpannedChar {
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
