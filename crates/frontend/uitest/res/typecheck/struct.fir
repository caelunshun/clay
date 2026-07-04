mod pip {
    pub struct Meow {
        pub a: u32,
        b: i32,
    }

    pub struct Mew(u32, pub i32);
}

use pip::*;

fn main() {
    Mew {}
}
