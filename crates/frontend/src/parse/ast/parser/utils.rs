use crate::{
    base::{
        LeafDiag, Level, Session,
        syntax::{Matcher as _, Span},
    },
    parse::{
        ast::{
            Keyword, PunctSeq,
            entry::{C, P},
        },
        token::{
            GroupDelimiter, Ident, Lifetime, Punct, TokenCharLit, TokenGroup, TokenMatcher,
            TokenNumLit, TokenPunct, TokenStrLit, token_matcher,
        },
    },
    punct, symbol,
};

pub fn match_any_ident(c: C) -> Option<Ident> {
    c.lookahead(|c| Some(*c.eat()?.ident()?))
}

pub fn match_kw(kw: Keyword) -> impl TokenMatcher<Output = Option<Ident>> {
    token_matcher(kw.expectation_name(), move |c, _h| {
        match_any_ident(c).filter(|v| !v.raw && v.text == kw.symbol())
    })
}

pub fn match_ident() -> impl TokenMatcher<Output = Option<Ident>> {
    token_matcher(symbol!("identifier"), move |c, h| {
        let ident = match_any_ident(c)?;

        if ident.raw {
            return Some(ident);
        }

        if Keyword::try_new(ident.text.as_str(&Session::fetch())).is_some() {
            h.hint(LeafDiag::new(
                Level::Note,
                format_args!("`{}` is a reserved keyword", ident.text),
            ));

            return None;
        }

        Some(ident)
    })
}

pub fn match_group(group: GroupDelimiter) -> impl TokenMatcher<Output = Option<TokenGroup>> {
    token_matcher(group.opening_name(), move |c, _| {
        Some(c.eat()?.group().filter(|v| v.delimiter == group)?.clone())
    })
}

pub fn match_eos(p: P) -> bool {
    let closing_name = p.cursor_unsafe().iter.group().delimiter.closing_name();

    p.expect(closing_name, |v| v.eat().is_none())
}

pub fn match_punct(punct: Punct) -> impl TokenMatcher<Output = Option<TokenPunct>> {
    token_matcher(punct.expectation_name(), move |c, _| {
        c.eat()
            .and_then(|v| v.punct())
            .filter(|v| v.ch == punct)
            .copied()
    })
}

pub fn match_punct_seq(punct: PunctSeq) -> impl TokenMatcher<Output = Option<Span>> {
    token_matcher(punct.expectation_name(), move |c, _| {
        let start = c.next_span();

        if punct
            .seq()
            .iter()
            .all(|&v| match_punct(v).consume(c).is_some())
        {
            Some(start.to(c.prev_span()))
        } else {
            None
        }
    })
}

pub fn match_str_lit() -> impl TokenMatcher<Output = Option<TokenStrLit>> {
    token_matcher(symbol!("string literal"), |c, _| {
        c.eat().and_then(|v| v.str_lit()).copied()
    })
}

pub fn match_char_lit() -> impl TokenMatcher<Output = Option<TokenCharLit>> {
    token_matcher(symbol!("character literal"), |c, _| {
        c.eat().and_then(|v| v.char_lit()).copied()
    })
}

pub fn match_num_lit() -> impl TokenMatcher<Output = Option<TokenNumLit>> {
    token_matcher(symbol!("numeric literal"), |c, _| {
        c.eat().and_then(|v| v.num_lit()).copied()
    })
}

pub fn match_lifetime() -> impl TokenMatcher<Output = Option<Lifetime>> {
    token_matcher(symbol!("lifetime"), |c, _| {
        c.eat().and_then(|v| v.lifetime()).copied()
    })
}

pub struct Delimited<E> {
    pub elems: Vec<E>,
    pub trailing: bool,
}

impl<E> Delimited<E> {
    pub fn is_multi(&self) -> bool {
        self.elems.len() != 1 || self.trailing
    }

    pub fn into_singleton(mut self) -> Result<E, Vec<E>> {
        if !self.is_multi() {
            Ok(self.elems.pop().unwrap())
        } else {
            Err(self.elems)
        }
    }
}

pub fn parse_delimited_until_terminator<C: ?Sized, E>(
    p: P,
    cx: &mut C,
    mut match_elem: impl FnMut(P, &mut C) -> E,
    mut match_delimiter: impl FnMut(P, &mut C) -> bool,
    mut match_terminator: impl FnMut(P, &mut C) -> bool,
) -> Delimited<E> {
    let mut elems = Vec::new();

    let trailing = loop {
        if match_terminator(p, cx) {
            break !elems.is_empty();
        }

        elems.push(match_elem(p, cx));

        if match_terminator(p, cx) {
            break false;
        }

        if !match_delimiter(p, cx) {
            if !match_terminator(p, cx) {
                // Recovery strategy: ignore.
                p.stuck_recover_with(|_| {});
            }

            break false;
        }
    };

    Delimited { elems, trailing }
}

pub fn parse_comma_group<E>(p: P, mut match_elem: impl FnMut(P) -> E) -> Delimited<E> {
    parse_delimited_until_terminator(
        p,
        &mut (),
        |p, _| match_elem(p),
        |p, _| match_punct(punct!(',')).expect(p).is_some(),
        |p, _| match_eos(p),
    )
}
