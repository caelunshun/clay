use super::{
    GroupDelimiter, Ident, Punct, StrLitKind, TokenCharLit, TokenGroup, TokenPunct, TokenStrLit,
    TokenStream, TokenTree,
};
use crate::{
    base::{
        Diag, LeafDiag, Session,
        syntax::{CharCursor, CharParser, Parser, RawCharCursor, Span, Symbol},
    },
    parse::token::{IntegralKind, Lifetime, NumLitBase, TokenNumLit, TokenNumLitKind, punct},
    semantic::syntax::{FloatKind, IntKind},
    symbol,
};
use unicode_xid::UnicodeXID;

type P<'a, 'ch> = &'a mut CharParser<'ch>;
type C<'a, 'ch> = &'a mut CharCursor<'ch>;

pub fn tokenize(span: Span) -> TokenGroup {
    let text = Session::fetch().source_map.file(span.lo).text(span);
    let mut parser = Parser::new(RawCharCursor::new(span, &text));
    let p = &mut parser;

    if p.expect(symbol!("byte order mark"), |c| match_ch(c, '\u{feff}')) {
        // (ignore it)
    }

    parse_group(p, p.next_span(), GroupDelimiter::File)
}

#[derive(Default)]
struct GroupBuilder {
    stream: TokenStream,
    glued: bool,
}

impl GroupBuilder {
    fn push(&mut self, token: impl Into<TokenTree>) {
        self.glued = true;
        self.stream.push(token);
    }

    fn push_space(&mut self) {
        self.glued = false;
    }

    pub fn glued_punct(&self) -> Option<&TokenPunct> {
        self.stream
            .last()
            .and_then(|v| v.punct())
            .filter(|_| self.glued)
    }

    pub fn glued_num(&self) -> Option<&TokenNumLit> {
        self.stream
            .last()
            .and_then(|v| v.num_lit())
            .filter(|_| self.glued)
    }
}

fn parse_group(p: P, group_start: Span, delimiter: GroupDelimiter) -> TokenGroup {
    let mut builder = GroupBuilder::default();

    'parse: loop {
        let token_start = p.next_span();

        p.recover_chomp();

        // Parse closing group delimiters
        if let Some(closing_del) = p.expect(delimiter.closing_name(), |c| {
            GroupDelimiter::CLOSEABLE
                .iter()
                .copied()
                .find(|v| match_ch_or_eof(c, v.closing()))
        }) {
            if closing_del != delimiter {
                Diag::span_err(
                    token_start,
                    format_args!(
                        "{} delimiter; expected {}, got {}",
                        if closing_del == GroupDelimiter::File {
                            "unclosed"
                        } else {
                            "mismatched"
                        },
                        delimiter.closing_name(),
                        closing_del.closing_name()
                    ),
                )
                .child(LeafDiag::span_note(group_start, "opening delimiter here"))
                .emit();
            }

            break;
        }

        // Parse opening group delimiters
        for open_del in GroupDelimiter::OPENABLE {
            if p.expect(open_del.opening_name(), |c| match_ch(c, open_del.opening())) {
                builder.push(parse_group(p, token_start, open_del));

                continue 'parse;
            }
        }

        // Parse comments
        if p.expect(symbol!("`//`"), |c| {
            c.eat() == Some('/') && c.eat() == Some('/')
        }) {
            while p.expect(symbol!("commented character"), |c| {
                c.eat().is_none_or(|v| v != '\n')
            }) {
                // (continue eating)
            }

            continue;
        }

        if p.expect(symbol!("`/*`"), |c| {
            c.eat() == Some('/') && c.eat() == Some('*')
        }) {
            let mut depth = 1;

            while depth > 0 {
                if p.expect(symbol!("`/*`"), |c| {
                    c.eat() == Some('/') && c.eat() == Some('*')
                }) {
                    depth += 1;
                    continue;
                }

                if p.expect(symbol!("`*/`"), |c| {
                    c.eat() == Some('*') && c.eat() == Some('/')
                }) {
                    depth -= 1;
                    continue;
                }

                if p.expect(symbol!("commented character"), |c| c.eat().is_some()) {
                    continue;
                }

                p.stuck().ignore_about_to_break();
                break;
            }

            continue;
        }

        // Parse identifiers (and prefixed string literals)
        if let Some(ident) = parse_ident(p, builder.glued_num().is_none()) {
            if let Some(glued) = builder.glued_num() {
                Diag::span_err(
                    ident.span,
                    "identifier cannot come immediately after numeric literal",
                )
                .secondary(glued.span, "numeric literal here")
                .emit();
            }

            // Try to parse a string literal
            let mut pounds = 0;

            while p.expect(symbol!("`#`"), |c| match_ch(c, '#')) {
                pounds += 1;
            }

            if let Some(str) = parse_string_lit(p, Some(ident), pounds, token_start) {
                builder.push(str);
                continue;
            }

            // Otherwise, parse it as an identifier.
            if pounds == 0 {
                // Parse identifier
                builder.push(ident);
                continue;
            } else {
                // Has to be a string :(
                if p.stuck().should_break() {
                    break;
                }

                continue;
            }
        }

        // Parse un-prefixed string literals
        if let Some(str) = parse_string_lit(p, None, 0, token_start) {
            builder.push(str);
            continue;
        }

        // Parse numeric literals
        if parse_num_lit(p, &mut builder) {
            continue;
        }

        // Parse character or lifetime
        if let Some(v) = parse_char_lit_or_lifetime(p) {
            builder.push(v);
            continue;
        }

        // Parse punctuation
        if let Some(ch) = p.expect(symbol!("punctuation"), |c| match_chs(c, Punct::CHARSET)) {
            builder.push(TokenPunct {
                span: token_start,
                ch: Punct::new(ch),
                glued: builder.glued_punct().is_some(),
            });

            continue;
        }

        // Parse whitespace.
        if p.expect(symbol!("whitespace"), |c| {
            c.eat().is_some_and(|c| c.is_whitespace())
        }) {
            builder.push_space();
            continue;
        }

        // We're stuck :(
        if p.stuck().should_break() {
            break;
        }

        builder.push_space();
    }

    TokenGroup {
        span: group_start.to(p.prev_span()),
        delimiter,
        tokens: builder.stream,
    }
}

fn parse_ident(p: P, visible: bool) -> Option<Ident> {
    let start = p.next_span();

    let first_ch = p.expect_covert(visible, symbol!("identifier"), match_ident_first_char)?;

    let mut accum = String::new();

    let raw = if first_ch == '\\' {
        true
    } else {
        accum.push(first_ch);
        false
    };

    while let Some(ch) = p.expect(symbol!("identifier character"), |c| {
        c.eat().filter(|c| c.is_xid_continue())
    }) {
        accum.push(ch);
    }

    if raw && accum.is_empty() {
        Diag::span_err(
            start,
            "expected identifier character after escape character",
        )
        .emit();

        return None;
    }

    Some(
        Ident {
            span: start.to(p.prev_span()),
            text: Symbol::new(&accum),
            raw,
        }
        .into(),
    )
}

fn match_ident_first_char(c: C) -> Option<char> {
    c.lookahead(|c| {
        c.eat()
            .filter(|&c| c.is_xid_start() || c == '_' || c == '\\')
    })
}

fn parse_string_lit(
    p: P,
    prefix: Option<Ident>,
    mut pounds: u32,
    prefix_start: Span,
) -> Option<TokenStrLit> {
    let quote_start = p.next_span();

    // Match the opening quote
    if !p.expect(symbol!("`\"`"), |c| match_ch(c, '"')) {
        return None;
    }

    // Interpret the prefix
    let (kind, is_raw) = 'prefix: {
        let Some(prefix) = prefix else {
            break 'prefix (StrLitKind::Utf8Slice, false);
        };

        if prefix.raw {
            Diag::span_err(prefix.span, "unknown string literal prefix")
                .child(LeafDiag::span_note(
                    prefix.span.truncate_left(1),
                    "`@`, the raw identifier indicator, is not expected in any string prefix",
                ))
                .emit();

            break 'prefix (StrLitKind::Utf8Slice, false);
        }

        let (prefix_sym, is_raw) = if let Some(prefix_sym) = prefix
            .text
            .as_str(&Session::fetch())
            .strip_prefix('r')
            .map(Symbol::new)
        {
            (prefix_sym, true)
        } else {
            (prefix.text, false)
        };

        let Some(lit_kind) = StrLitKind::VARIANTS
            .into_iter()
            .find(|v| v.prefix() == prefix_sym)
        else {
            Diag::span_err(
                prefix.span,
                format_args!("unknown string literal prefix `{prefix_sym}`"),
            )
            .emit();

            break 'prefix (StrLitKind::Utf8Slice, false);
        };

        (lit_kind, is_raw)
    };

    if pounds > 0 && !is_raw {
        Diag::span_err(
            prefix_start.until(quote_start),
            "cannot surround a string literal with `#`s when the string is not raw",
        )
        .emit();

        pounds = 0;
    }

    // Parse the string contents
    let mut accum = String::new();

    let closing_name = if pounds == 0 {
        symbol!("`\"`")
    } else {
        let mut accum = String::new();
        accum.push_str("`\"");
        for _ in 0..pounds {
            accum.push('#');
        }
        accum.push('`');
        Symbol::new(&accum)
    };

    loop {
        // Match closing quote
        if p.expect(closing_name, |c| {
            if !match_ch(c, '"') {
                return false;
            }

            for _ in 0..pounds {
                if !match_ch(c, '#') {
                    return false;
                }
            }

            true
        }) {
            break;
        }

        // Match escape
        if !is_raw && let Some(ch) = parse_char_escape(p) {
            accum.push(ch);
            continue;
        }

        // Match regular character
        if let Some(ch) = parse_regular_char(p) {
            accum.push(ch);
            continue;
        }

        p.stuck().ignore_about_to_break();

        break;
    }

    Some(TokenStrLit {
        span: prefix_start.to(p.prev_span()),
        kind,
        value: Symbol::new(&accum),
    })
}

fn parse_char_lit_or_lifetime(p: P) -> Option<TokenTree> {
    let start = p.next_span();

    if !p.expect(symbol!("`'`"), |c| match_ch(c, '\'')) {
        return None;
    }

    let mut accum = String::new();
    let mut accum_no_escapes = true;
    let mut char_count = 0;

    loop {
        // Match closing quote
        if p.expect_covert(char_count == 1, symbol!("`'`"), |c| match_ch(c, '\'')) {
            if char_count != 1 {
                Diag::span_err(
                    start.to(p.prev_span()),
                    "expected single character in character literal",
                )
                .emit();
            }

            return Some(
                TokenCharLit {
                    span: start.to(p.prev_span()),
                    value: accum.chars().next().unwrap_or('?'),
                }
                .into(),
            );
        }

        // Match escape
        if let Some(ch) = parse_char_escape(p) {
            accum.push(ch);
            char_count += 1;
            accum_no_escapes = false;
            continue;
        }

        // Match first character (can be anything)
        if accum.is_empty() {
            if let Some(ch) = parse_regular_char(p) {
                accum.push(ch);
                char_count += 1;
                continue;
            } else {
                p.stuck().ignore_about_to_break();
                return None;
            }
        }

        // Match subsequent lifetime characters.
        if let Some(ch) = p.expect(symbol!("lifetime character"), |c| {
            c.eat().filter(|c| c.is_xid_continue())
        }) {
            accum.push(ch);
            char_count += 1;
            continue;
        }

        // Otherwise, we've finished our lifetime.
        if !accum_no_escapes {
            Diag::span_err(start.to(p.prev_span()), "lifetime cannot contain escapes").emit();
        }

        if !accum.chars().next().unwrap().is_xid_start() && accum.chars().next().unwrap() != '_' {
            Diag::span_err(
                start.to(p.prev_span()),
                "lifetime cannot start with that character",
            )
            .emit();
        }

        return Some(
            Lifetime {
                span: start.to(p.prev_span()),
                name: Symbol::new(&accum),
            }
            .into(),
        );
    }
}

fn parse_char_escape(p: P) -> Option<char> {
    let start = p.next_span();

    if !p.expect(symbol!("`\\`"), |c| match_ch(c, '\\')) {
        return None;
    }

    // Match well-known escapes
    let well_known = [
        (symbol!("`r`"), 'r', '\r'),
        (symbol!("`n`"), 'n', '\n'),
        (symbol!("`t`"), 't', '\t'),
        (symbol!("`0`"), '0', '\0'),
        (symbol!("`\"`"), '"', '"'),
        (symbol!("`'`"), '\'', '\''),
    ];

    for (name, ch, escape) in well_known {
        if p.expect(name, |c| match_ch(c, ch)) {
            return Some(escape);
        }
    }

    // Match ASCII escapes
    if p.expect(symbol!("`x`"), |c| match_ch(c, 'x')) {
        let Some(hexits) = p.expect(symbol!("hexadecimal ASCII code"), |c| {
            Some([
                c.eat().filter(|c| c.is_ascii_hexdigit())?,
                c.eat().filter(|c| c.is_ascii_hexdigit())?,
            ])
        }) else {
            p.stuck().ignore_not_in_loop();

            return None;
        };

        let hex_seq = [hexits[0] as u8, hexits[1] as u8];
        let hex_seq = std::str::from_utf8(&hex_seq).unwrap(); // Hexits are ASCII

        let code = u8::from_str_radix(hex_seq, 16).unwrap();

        if code > 0x7F {
            Diag::span_err(
                start.to(p.prev_span()),
                "ASCII escape code must be at most `\\x7F`",
            )
            .emit();

            return Some('?');
        }

        return Some(code as char);
    }

    // Match Unicode escapes
    if p.expect(symbol!("`u`"), |c| match_ch(c, 'u')) {
        todo!()
    }

    p.stuck().ignore_not_in_loop();

    None
}

fn parse_regular_char(p: P) -> Option<char> {
    p.expect(symbol!("character"), |c| c.eat())
}

#[must_use]
fn parse_num_lit(p: P, builder: &mut GroupBuilder) -> bool {
    fn expect_digit(p: P, base: NumLitBase) -> Option<char> {
        p.expect(base.digit_name(), |c| {
            c.eat().filter(|&v| v.is_digit(base.radix()))
        })
    }

    fn match_integral_part(p: P, base: NumLitBase, accum: &mut String) {
        loop {
            if p.expect(symbol!("`_`"), |c| match_ch(c, '_')) {
                continue;
            }

            if let Some(digit) = expect_digit(p, base) {
                accum.push(digit);
                continue;
            }

            break;
        }
    }

    let start = p.next_span();

    // Match first digit
    let Some(first_digit) = p.expect(symbol!("digit"), |c| c.eat().filter(|v| v.is_ascii_digit()))
    else {
        return false;
    };

    // Match base prefix
    let mut int_part = String::new();

    let base = 'base: {
        if first_digit != '0' {
            int_part.push(first_digit);
            break 'base NumLitBase::Decimal;
        }

        if p.expect(symbol!("`x`"), |c| match_ch(c, 'x')) {
            break 'base NumLitBase::Hexadecimal;
        }

        if p.expect(symbol!("`o`"), |c| match_ch(c, 'o')) {
            break 'base NumLitBase::Octal;
        }

        if p.expect(symbol!("`b`"), |c| match_ch(c, 'b')) {
            break 'base NumLitBase::Binary;
        }

        int_part.push(first_digit);
        NumLitBase::Decimal
    };

    // Match integral part
    match_integral_part(p, base, &mut int_part);
    let int_part = Symbol::new(&int_part);

    // If this is potentially a floating point number...
    if base != NumLitBase::Decimal {
        let suffix = parse_num_lit_suffix(p)
            .filter(|&(span, kind)| match kind {
                IntegralKind::Int(_) | IntegralKind::Uint(_) => true,
                IntegralKind::Float(_) => {
                    Diag::span_err(
                        span,
                        format_args!("{} float literal is not supported", base.name()),
                    )
                    .emit();
                    false
                }
            })
            .map(|v| v.1);

        builder.push(TokenNumLit {
            span: start.to(p.prev_span()),
            kind: TokenNumLitKind::Integral {
                base,
                value: int_part,
                suffix,
            },
        });

        return true;
    }

    // Match the period.
    let dec_part = if p.expect(symbol!("`.`"), |c| match_ch(c, '.')) {
        let first_period_sp = p.prev_span();

        // This could either be...
        //
        // 1. A regular floating point number (e.g. `123.456`)
        // 2. A floating point number without the suffix (e.g. `123. `, `123.+`, etc)
        // 3. A method call on a number (e.g. `123.sin()`)
        // 4. A range operation (e.g. `1..6`)
        //
        // In the case of `((,),).0.0`, we parse `0.0` as a floating point number and let the
        // parser split it up into two field accesses.
        //
        // We only have to handle the 3rd and 4th cases specially, which we do here...
        if let Some(ident) = parse_ident(p, true) {
            builder.push(TokenNumLit {
                span: start.to(p.prev_span()),
                kind: TokenNumLitKind::Integral {
                    base,
                    value: int_part,
                    suffix: None,
                },
            });

            builder.push(TokenPunct {
                span: first_period_sp,
                ch: punct!('.'),
                glued: false,
            });

            builder.push(ident);

            return true;
        }

        if p.expect(symbol!("`.`"), |c| match_ch(c, '.')) {
            builder.push(TokenNumLit {
                span: start.to(p.prev_span()),
                kind: TokenNumLitKind::Integral {
                    base,
                    value: int_part,
                    suffix: None,
                },
            });

            builder.push(TokenPunct {
                span: first_period_sp,
                ch: punct!('.'),
                glued: false,
            });

            builder.push(TokenPunct {
                span: p.prev_span(),
                ch: punct!('.'),
                glued: true,
            });

            return true;
        }

        // Match the decimal portion.
        let mut accum = String::new();
        match_integral_part(p, base, &mut accum);
        Some(Symbol::new(&accum))
    } else {
        None
    };

    // Match an `e` or `E`.
    let exp_part = if p.expect(symbol!("`E`"), |c| match_ch(c, 'E'))
        || p.expect(symbol!("`e`"), |c| match_ch(c, 'e'))
    {
        let mut accum = String::new();

        // Match the sign.
        if p.expect(symbol!("`+`"), |c| match_ch(c, '+')) {
            accum.push('+');
        }

        if p.expect(symbol!("`-`"), |c| match_ch(c, '-')) {
            accum.push('-');
        }

        // Match the exponential portion.
        match_integral_part(p, base, &mut accum);
        Some(Symbol::new(&accum))
    } else {
        None
    };

    let suffix = parse_num_lit_suffix(p);

    if dec_part.is_some() || exp_part.is_some() {
        let suffix = suffix.and_then(|(span, suffix)| {
            let IntegralKind::Float(suffix) = suffix else {
                Diag::span_err(span, "cannot use integer suffix for floating-point literal").emit();
                return None;
            };

            Some(suffix)
        });

        builder.push(TokenNumLit {
            span: start.to(p.prev_span()),
            kind: TokenNumLitKind::Floating {
                int_part,
                dec_part,
                exp_part,
                suffix,
            },
        });
    } else {
        builder.push(TokenNumLit {
            span: start.to(p.prev_span()),
            kind: TokenNumLitKind::Integral {
                base,
                value: int_part,
                suffix: suffix.map(|v| v.1),
            },
        });
    }

    true
}

fn parse_num_lit_suffix(p: P) -> Option<(Span, IntegralKind)> {
    let s = &Session::fetch();

    let ident = parse_ident(p, true)?;

    if ident.raw {
        Diag::span_err(
            ident.span,
            "raw identifier not expected after numeric literal",
        )
        .emit();

        return None;
    }

    [
        ("i8", IntegralKind::Int(IntKind::S8)),
        ("u8", IntegralKind::Uint(IntKind::S8)),
        ("i16", IntegralKind::Int(IntKind::S16)),
        ("u16", IntegralKind::Uint(IntKind::S16)),
        ("i32", IntegralKind::Int(IntKind::S32)),
        ("u32", IntegralKind::Uint(IntKind::S32)),
        ("i64", IntegralKind::Int(IntKind::S64)),
        ("u64", IntegralKind::Uint(IntKind::S64)),
        ("f32", IntegralKind::Float(FloatKind::S32)),
        ("f64", IntegralKind::Float(FloatKind::S64)),
    ]
    .into_iter()
    .find(|&(text, _kind)| text == ident.text.as_str(s))
    .map(|v| (ident.span, v.1))
}

fn match_ch(c: C, ch: char) -> bool {
    match_ch_or_eof(c, Some(ch))
}

fn match_ch_or_eof(c: C, ch: Option<char>) -> bool {
    c.lookahead(|c| c.eat() == ch)
}

fn match_chs(c: C, set: &str) -> Option<char> {
    c.lookahead(|c| c.eat().filter(|&v| set.contains(v)))
}
