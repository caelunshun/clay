use crate::sexpr::SExpr;
use compact_str::CompactString;

pub fn parse_sexpr(input: &str) -> Option<SExpr> {
    let mut parser = Parser::new(input);
    let result = parser.parse_expr().flatten();
    if !parser.is_at_end() { None } else { result }
}

struct Parser<'a> {
    src: &'a str,
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(src: &'a str) -> Self {
        Self { src, pos: 0 }
    }

    fn is_at_end(&self) -> bool {
        self.pos >= self.src.len()
    }

    fn peek(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    fn next(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.pos += ch.len_utf8();
        Some(ch)
    }

    fn skip_ws(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.next();
            } else {
                break;
            }
        }
    }

    fn parse_expr(&mut self) -> Option<Option<SExpr>> {
        self.skip_ws();
        if self.is_at_end() {
            return Some(None);
        }

        match self.peek()? {
            '(' => {
                self.next();
                let mut elems = Vec::new();
                loop {
                    self.skip_ws();
                    if self.is_at_end() {
                        return None; // unterminated list
                    }
                    if self.peek()? == ')' {
                        self.next();
                        break;
                    }
                    elems.push(self.parse_expr()??);
                }
                Some(Some(SExpr::List(elems.into_boxed_slice())))
            }
            '"' => Some(Some(self.parse_string()?)),
            c if is_symbol_start(c) => Some(Some(self.parse_atom()?)),
            _ => None,
        }
    }

    fn parse_string(&mut self) -> Option<SExpr> {
        debug_assert_eq!(self.peek(), Some('"'));
        self.next(); // skeep quote

        let mut s = String::new();
        while let Some(c) = self.next() {
            match c {
                '"' => return Some(SExpr::String(CompactString::from(s))),
                '\\' => {
                    let esc = self.next()?;
                    s.push(match esc {
                        'n' => '\n',
                        'r' => '\r',
                        't' => '\t',
                        '\\' => '\\',
                        '"' => '"',
                        other => other,
                    });
                }
                _ => s.push(c),
            }
        }
        None // missing terminator
    }

    fn parse_atom(&mut self) -> Option<SExpr> {
        let start = self.pos;
        while let Some(c) = self.peek() {
            if c.is_whitespace() || c == '(' || c == ')' {
                break;
            }
            self.next();
        }

        let atom = &self.src[start..self.pos];
        if let Ok(i) = atom.parse::<i64>() {
            Some(SExpr::Int(i))
        } else if let Ok(f) = atom.parse::<f64>() {
            Some(SExpr::Float(f))
        } else {
            Some(SExpr::Symbol(CompactString::from(atom)))
        }
    }
}

fn is_symbol_start(c: char) -> bool {
    !c.is_whitespace() && c != '(' && c != ')'
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexpr::{float, int, list, string, symbol};

    #[test]
    fn test_basic() {
        let input = r#"(a 123 1.23 "str" (nested (1 2)))"#;
        let parsed = parse_sexpr(input).unwrap();
        assert_eq!(
            parsed,
            list([
                symbol("a"),
                int(123),
                float(1.23),
                string("str"),
                list([symbol("nested"), list([int(1), int(2)])])
            ])
        );
    }
}
