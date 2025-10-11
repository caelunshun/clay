use compact_str::CompactString;
use std::fmt::{Display, Formatter};

/// Interned identifier string.
#[salsa::interned(debug)]
pub struct Ident<'db> {
    #[returns(ref)]
    pub owned: OwnedIdent,
}

impl<'db> Ident<'db> {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OwnedIdent(CompactString);

impl OwnedIdent {
    pub fn new(s: impl Into<CompactString>) -> Option<Self> {
        let s = s.into();
        if is_valid_ident(&s) {
            Some(Self(s))
        } else {
            None
        }
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Display for OwnedIdent {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

pub fn is_valid_ident(s: &str) -> bool {
    for (i, c) in s.chars().enumerate() {
        if i == 0 {
            if !is_valid_first_char(c) {
                return false;
            }
        } else if !is_valid_remaininder_char(c) {
            return false;
        }
    }
    true
}

fn is_valid_first_char(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_valid_remaininder_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}
