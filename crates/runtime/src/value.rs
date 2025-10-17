/// Owned Rust representation of a fir value.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Unit,
    Int(i64),
    Real(f64),
    Bool(bool),
}
