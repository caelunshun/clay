use crate::{
    base::syntax::{Symbol, symbol},
    parse::token::{Punct, punct},
    utils::lang::{ConstFmt, const_str_eq},
};
use std::fmt;

// === Keywords === //

macro_rules! define_keywords {
    ($( $name:ident = $text:literal ),* $(,)?) => {
        #[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
        pub enum Keyword {
            $($name,)*
        }

        impl Keyword {
            pub const fn new(v: &str) -> Self {
                $(if const_str_eq(v, $text) {
                    return Self::$name;
                })*

                let mut f = ConstFmt::new();

                f.write('`');
                f.write_str(v);
                f.write_str("` is not a valid `Punct`");

                panic!("{}", f.finish());
            }

            pub fn try_new(v: &str) -> Option<Self> {
                match v {
                    $($text => Some(Self::$name),)*
                    _ => None,
                }
            }

            pub const fn str(self) -> &'static str {
                match self {
                    $(Self::$name => $text,)*
                }
            }

            pub fn symbol(self) -> Symbol {
                match self {
                    $(Self::$name => symbol!($text),)*
                }
            }

            pub fn expectation_name(self) -> Symbol {
                match self {
                    $(Self::$name => symbol!(concat!("`", $text, "`")),)*
                }
            }
        }
    };
}

impl fmt::Debug for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.str().fmt(f)
    }
}

define_keywords! {
    As = "as",
    Break = "break",
    Const = "const",
    Continue = "continue",
    Crate = "crate",
    Dyn = "dyn",
    Else = "else",
    Enum = "enum",
    False = "false",
    Fn = "fn",
    For = "for",
    Hole = "_",
    If = "if",
    Impl = "impl",
    In = "in",
    Let = "let",
    Loop = "loop",
    Match = "match",
    Mod = "mod",
    Move = "move",
    Mut = "mut",
    Priv = "priv",
    Pub = "pub",
    Ref = "ref",
    Return = "return",
    SelfLower = "self",
    SelfUpper = "Self",
    Static = "static",
    Struct = "struct",
    Super = "super",
    Trait = "trait",
    True = "true",
    Type = "type",
    Union = "union",
    Use = "use",
    While = "while",
}

#[macro_export]
macro_rules! kw {
    ($kw:expr) => {
        const { $crate::parse::ast::Keyword::new($kw) }
    };
}

pub use kw;

// === Punctuation sequences === //

macro_rules! define_punct_seqs {
    ($($name:ident = $($text:literal)*),* $(,)?) => {
        #[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
        pub enum PunctSeq {
            $($name,)*
        }

        impl PunctSeq {
            pub const fn new(v: &str) -> Self {
                $(if const_str_eq(v, concat!($($text),*)) {
                    return Self::$name;
                })*

                let mut f = ConstFmt::new();

                f.write('`');
                f.write_str(v);
                f.write_str("` is not a valid `Punct`");

                panic!("{}", f.finish());
            }

            pub fn try_new(v: &str) -> Option<Self> {
                match v {
                    $(concat!($($text),*) => Some(Self::$name),)*
                    _ => None,
                }
            }

            pub const fn seq(self) -> &'static [Punct] {
                match self {
                    $(Self::$name => &[$( punct!($text), )*],)*
                }
            }

            pub fn expectation_name(self) -> Symbol {
                match self {
                    $(Self::$name => symbol!(concat!(
                        "`",
                        $($text,)*
                        "`"
                    )),)*
                }
            }
        }
    };
}

define_punct_seqs! {
    Arrow = '-' '>',
    AssignAdd = '+' '=',
    AssignBitAnd = '&' '=',
    AssignBitOr = '|' '=',
    AssignBitXor = '^' '=',
    AssignDiv = '/' '=',
    AssignMul = '*' '=',
    AssignRem = '%' '=',
    AssignSub = '-' '=',
    BiDots = '.' '.',
    DotDotEq = '.' '.' '=',
    Geq = '>' '=',
    Leq = '<' '=',
    LogicalAnd = '&' '&',
    LogicalEq = '=' '=',
    LogicalNeq = '!' '=',
    LogicalOr = '|' '|',
    Pow = '^' '^',
    Shl = '<' '<',
    ShlAssign = '<' '<' '=',
    Shr = '>' '>',
    ShrAssign = '>' '>' '=',
    TriDots = '.' '.' '.',
    Turbo = ':' ':',
    WideArrow = '=' '>',
}

#[macro_export]
macro_rules! puncts {
    ($kw:expr) => {
        const { $crate::parse::ast::PunctSeq::new($kw) }
    };
}

pub use puncts;
