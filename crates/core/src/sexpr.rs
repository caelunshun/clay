//! Simple S-expression parsing and formatting tooling,
//! primarily used for test cases at various levels of the IR.

use compact_str::CompactString;
use std::fmt::{Display, Formatter, Write as _};

#[derive(Debug, Clone, PartialEq)]
pub enum SExpr {
    Int(i64),
    Float(f64),
    Symbol(CompactString),
    String(CompactString),
    List(Box<[SExpr]>),
}

impl SExpr {
    fn format(&self, dst: &mut String, indent_level: usize) {
        match self {
            SExpr::Int(x) => write!(dst, "{}", x).unwrap(),
            SExpr::Float(x) => write!(dst, "{}", x).unwrap(),
            SExpr::Symbol(x) => write!(dst, "{}", x).unwrap(),
            SExpr::String(s) => write!(dst, "\"{}\"", escape_string(s)).unwrap(),
            SExpr::List(l) => {
                if !dst.ends_with('\n') && !dst.is_empty() {
                    dst.push('\n');
                    write!(dst, "{}", "    ".repeat(indent_level)).unwrap();
                }
                write!(dst, "(").unwrap();
                for (i, e) in l.iter().enumerate() {
                    e.format(dst, indent_level + 1);
                    if i != l.len() - 1 {
                        write!(dst, " ").unwrap();
                    }
                }
                write!(dst, ")").unwrap();
            }
        }
    }
}

fn escape_string(s: &str) -> String {
    let mut escaped = String::new();
    for c in s.chars() {
        escaped.extend(c.escape_default());
    }
    escaped
}

impl Display for SExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.format(&mut s, 0);

        // Remove trailing spaces
        let mut new_s = String::new();
        for line in s.lines() {
            new_s.push_str(line.trim_end());
            new_s.push('\n');
        }

        write!(f, "{new_s}")
    }
}

pub fn int(x: i64) -> SExpr {
    SExpr::Int(x)
}

pub fn float(x: f64) -> SExpr {
    SExpr::Float(x)
}

pub fn symbol(x: impl Into<CompactString>) -> SExpr {
    SExpr::Symbol(x.into())
}

pub fn string(x: impl Into<CompactString>) -> SExpr {
    SExpr::String(x.into())
}

pub fn list(es: impl IntoIterator<Item = SExpr>) -> SExpr {
    SExpr::List(es.into_iter().collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use indoc::indoc;

    #[test]
    fn formatting() {
        let expr = list([
            string("Hi there\n"),
            int(3),
            list([
                float(10.1),
                symbol("Ozymandias"),
                list([symbol("item"), int(10)]),
            ]),
            int(5),
        ]);
        assert_eq!(
            expr.to_string(),
            indoc! {r#"
        ("Hi there\n" 3
            (10.1 Ozymandias
                (item 10)) 5)
        "#}
        )
    }
}
