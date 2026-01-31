pub enum Option<T> {
    Some(T),
    None,
}

pub use Option::*;

fn main() {
    if let a = &2 {
        a = &4;
    }
}
