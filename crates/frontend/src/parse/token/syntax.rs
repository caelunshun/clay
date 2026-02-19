use crate::{
    base::{
        Session,
        syntax::{
            AtomSimplify, Cursor, Delimited, HasSpan, LookaheadResult, Matcher, Parser, Span,
            StuckHinter, Symbol,
        },
    },
    parse::ast::Keyword,
    symbol,
    utils::lang::ConstFmt,
};
use std::{ops::Deref, rc::Rc, slice, str};

// === TokenStream === //

#[derive(Debug, Clone, Default)]
pub struct TokenStream(Rc<Vec<TokenTree>>);

impl TokenStream {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn tokens_mut(&mut self) -> &mut Vec<TokenTree> {
        Rc::make_mut(&mut self.0)
    }

    pub fn push(&mut self, token: impl Into<TokenTree>) {
        self.tokens_mut().push(token.into());
    }
}

impl Deref for TokenStream {
    type Target = [TokenTree];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> IntoIterator for &'a TokenStream {
    type Item = &'a TokenTree;
    type IntoIter = slice::Iter<'a, TokenTree>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

// === TokenTree === //

#[derive(Debug, Clone)]
pub enum TokenTree {
    Group(TokenGroup),
    Ident(Ident),
    Lifetime(Lifetime),
    Punct(TokenPunct),
    NumLit(TokenNumLit),
    StrLit(TokenStrLit),
    CharLit(TokenCharLit),
}

impl AtomSimplify for TokenTree {
    type Simplified = Self;

    fn simplify(self) -> Self::Simplified {
        self
    }

    fn is_eos(&self) -> bool {
        false
    }
}

impl HasSpan for TokenTree {
    fn span(&self) -> Span {
        match self {
            Self::Group(v) => v.span(),
            Self::Ident(v) => v.span(),
            Self::Lifetime(v) => v.span(),
            Self::Punct(v) => v.span(),
            Self::NumLit(v) => v.span(),
            Self::StrLit(v) => v.span(),
            Self::CharLit(v) => v.span(),
        }
    }
}

macro_rules! token_tree_converters {
    ($($variant:ident: $ty:ty),*$(,)?) => {
        $(
            impl From<$ty> for TokenTree {
                fn from(value: $ty) -> Self {
                    Self::$variant(value)
                }
            }
        )*

        paste::paste! {
            impl TokenTree {
                $(
                    pub fn [<$variant:snake>](&self) -> Option<&$ty> {
                        match self {
                            Self::$variant(v) => Some(v),
                            _ => None,
                        }
                    }

                    pub fn [<$variant:snake _mut>](&mut self) -> Option<&mut $ty> {
                        match self {
                            Self::$variant(v) => Some(v),
                            _ => None,
                        }
                    }

                    pub fn [<into_$variant:snake>](self) -> Result<$ty, Self> {
                        match self {
                            Self::$variant(v) => Ok(v),
                            v => Err(v),
                        }
                    }
                )*
            }
        }
    };
}

token_tree_converters! {
    Group: TokenGroup,
    Ident: Ident,
    Lifetime: Lifetime,
    Punct: TokenPunct,
    NumLit: TokenNumLit,
    StrLit: TokenStrLit,
    CharLit: TokenCharLit,
}

#[derive(Debug, Clone)]
pub struct TokenGroup {
    pub span: Span,
    pub delimiter: GroupDelimiter,
    pub tokens: TokenStream,
}

impl HasSpan for TokenGroup {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum GroupDelimiter {
    Brace,
    Bracket,
    Paren,
    File,
    Macro,
}

impl GroupDelimiter {
    pub const OPENABLE: [Self; 3] = [Self::Brace, Self::Bracket, Self::Paren];
    pub const CLOSEABLE: [Self; 4] = [Self::Brace, Self::Bracket, Self::Paren, Self::File];

    pub fn opening(self) -> char {
        match self {
            GroupDelimiter::Brace => '{',
            GroupDelimiter::Bracket => '[',
            GroupDelimiter::Paren => '(',
            GroupDelimiter::File | GroupDelimiter::Macro => unreachable!(),
        }
    }

    pub fn opening_name(self) -> Symbol {
        match self {
            GroupDelimiter::Brace => symbol!("`{`"),
            GroupDelimiter::Bracket => symbol!("`[`"),
            GroupDelimiter::Paren => symbol!("`(`"),
            GroupDelimiter::File | GroupDelimiter::Macro => unreachable!(),
        }
    }

    pub fn closing(self) -> Option<char> {
        match self {
            GroupDelimiter::Brace => Some('}'),
            GroupDelimiter::Bracket => Some(']'),
            GroupDelimiter::Paren => Some(')'),
            GroupDelimiter::File => None,
            GroupDelimiter::Macro => unreachable!(),
        }
    }

    pub fn closing_name(self) -> Symbol {
        match self {
            GroupDelimiter::Brace => symbol!("`}`"),
            GroupDelimiter::Bracket => symbol!("`]`"),
            GroupDelimiter::Paren => symbol!("`)`"),
            GroupDelimiter::File => symbol!("end-of-file"),
            GroupDelimiter::Macro => unreachable!(),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct Ident {
    pub span: Span,
    pub text: Symbol,
    pub raw: bool,
}

impl Ident {
    pub fn new(span: Span, text: Symbol) -> Self {
        Self {
            span,
            text,
            raw: true,
        }
    }

    pub fn matches_unescaped(self, kw: Symbol) -> bool {
        !self.raw && self.text == kw
    }

    pub fn matches_kw(self, kw: Keyword) -> bool {
        self.matches_unescaped(kw.symbol())
    }
}

impl HasSpan for Ident {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct Lifetime {
    pub span: Span,
    pub name: Symbol,
}

impl HasSpan for Lifetime {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct TokenPunct {
    pub span: Span,
    pub ch: Punct,
    pub glued: bool,
}

impl HasSpan for TokenPunct {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Copy, Clone)]
pub struct TokenStrLit {
    pub span: Span,
    pub kind: StrLitKind,
    pub value: Symbol,
}

impl HasSpan for TokenStrLit {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum StrLitKind {
    Utf8Slice,
    ByteLiteral,
    NulTerminated,
}

impl StrLitKind {
    pub const VARIANTS: [Self; 3] = [Self::Utf8Slice, Self::ByteLiteral, Self::NulTerminated];

    pub fn prefix(self) -> Symbol {
        match self {
            Self::Utf8Slice => symbol!(""),
            Self::ByteLiteral => symbol!("b"),
            Self::NulTerminated => symbol!("c"),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct TokenNumLit {
    pub span: Span,
    pub text: Symbol,
}

impl TokenNumLit {
    pub fn base(self) -> NumLitBase {
        let session = Session::fetch();
        let text = self.text.as_str(&session);

        if text.starts_with("0x") {
            return NumLitBase::Hexadecimal;
        }

        if text.starts_with("0b") {
            return NumLitBase::Binary;
        }

        if text.starts_with("0o") {
            return NumLitBase::Octal;
        }

        NumLitBase::Decimal
    }
}

impl HasSpan for TokenNumLit {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum NumLitBase {
    Decimal,
    Binary,
    Hexadecimal,
    Octal,
}

impl NumLitBase {
    pub fn digit_name(self) -> Symbol {
        match self {
            NumLitBase::Decimal => symbol!("decimal digit"),
            NumLitBase::Binary => symbol!("binary digit"),
            NumLitBase::Hexadecimal => symbol!("hexadecimal digit"),
            NumLitBase::Octal => symbol!("octal digit"),
        }
    }

    pub fn radix(self) -> u32 {
        match self {
            NumLitBase::Decimal => 10,
            NumLitBase::Binary => 2,
            NumLitBase::Hexadecimal => 16,
            NumLitBase::Octal => 8,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct TokenCharLit {
    pub span: Span,
    pub value: char,
}

impl HasSpan for TokenCharLit {
    fn span(&self) -> Span {
        self.span
    }
}

// === Punct === //

macro_rules! define_puncts {
    (
        $($name:ident = $ch:literal),*
        $(,)*
    ) => {
        #[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
        pub enum Punct {
            $($name),*
        }

        impl Punct {
            pub const CHARSET: &str = concat!($($ch),*);

            pub const fn try_new(ch: char) -> Option<Self> {
                match ch {
                    $($ch => Some(Self::$name),)*
                    _ => None
                }
            }

            pub const fn char(self) -> char {
                match self {
                    $(Self::$name => $ch,)*
                }
            }

            pub fn expectation_name(self) -> Symbol {
                match self {
                    $(Self::$name => symbol!(concat!("`", $ch, "`")),)*
                }
            }
        }
    };
}

impl Punct {
    pub const fn new(ch: char) -> Self {
        let Some(ch) = Self::try_new(ch) else {
            let mut f = ConstFmt::new();

            f.write('`');
            f.write(ch);
            f.write_str("` is not a valid `Punct`");

            panic!("{}", f.finish());
        };

        ch
    }
}

define_puncts! {
    Equals = '=',
    Lt = '<',
    Gt = '>',
    Exclaim = '!',
    Tilde = '~',
    Plus = '+',
    Minus = '-',
    Asterisk = '*',
    Slash = '/',
    Percent = '%',
    Caret = '^',
    Ampersand = '&',
    Pipe = '|',
    Arobase = '@',
    Period = '.',
    Comma = ',',
    Semicolon = ';',
    Colon = ':',
    Octothorpe = '#',
    Dollar = '$',
    Question = '?',
    SingleQuote = '\'',
}

#[macro_export]
macro_rules! punct {
    ($ch:expr) => {
        const { $crate::parse::token::Punct::new($ch) }
    };
}

pub use punct;

// === TokenCursor === //

pub type TokenParser<'g> = Parser<RawTokenCursor<'g>>;
pub type TokenCursor<'ch> = Cursor<RawTokenCursor<'ch>>;

#[derive(Debug, Clone)]
pub struct RawTokenCursor<'a> {
    group: &'a TokenGroup,
    tokens: std::slice::Iter<'a, TokenTree>,
}

impl<'a> RawTokenCursor<'a> {
    pub fn new(group: &'a TokenGroup) -> Self {
        Self {
            group,
            tokens: group.tokens.iter(),
        }
    }

    pub fn group(&self) -> &'a TokenGroup {
        self.group
    }
}

impl<'a> From<&'a TokenGroup> for RawTokenCursor<'a> {
    fn from(value: &'a TokenGroup) -> Self {
        Self::new(value)
    }
}

impl<'a> Iterator for RawTokenCursor<'a> {
    type Item = TokenCursorElement<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.tokens.next() {
            Some(token) => TokenCursorElement::Token(token),
            None => TokenCursorElement::Ending(self.end_span()),
        })
    }
}

impl Delimited for RawTokenCursor<'_> {
    fn start_span(&self) -> Span {
        Span::new_sized(self.group.span.lo, 1)
    }

    fn end_span(&self) -> Span {
        Span::new_sized(self.group.span.hi - 1u32, 1)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum TokenCursorElement<'a> {
    Ending(Span),
    Token(&'a TokenTree),
}

impl HasSpan for TokenCursorElement<'_> {
    fn span(&self) -> Span {
        match *self {
            TokenCursorElement::Ending(span) => span,
            TokenCursorElement::Token(token) => token.span(),
        }
    }
}

impl<'a> AtomSimplify for TokenCursorElement<'a> {
    type Simplified = Option<&'a TokenTree>;

    fn simplify(self) -> Self::Simplified {
        match self {
            TokenCursorElement::Ending(_) => None,
            TokenCursorElement::Token(token) => Some(token),
        }
    }

    fn is_eos(&self) -> bool {
        match self {
            TokenCursorElement::Ending(..) => true,
            TokenCursorElement::Token(..) => false,
        }
    }
}

pub trait TokenMatcher: for<'a> Matcher<RawTokenCursor<'a>> {}

impl<T> TokenMatcher for T where T: for<'a> Matcher<RawTokenCursor<'a>> {}

pub fn token_matcher<F, R>(name: Symbol, matcher: F) -> (Symbol, F)
where
    F: Fn(&mut Cursor<RawTokenCursor<'_>>, &mut StuckHinter<'_>) -> R,
    R: LookaheadResult,
{
    (name, matcher)
}
