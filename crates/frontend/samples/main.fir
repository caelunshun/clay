mod glob_test;

use glob_test::*;

pub struct MyStruct {
    foo: &mut u32,
    bar: &i32,
}

impl MyStruct {
    pub fn new() -> Self {
        Self {
            foo: &3,
            bar: &2,
        }
    }
}

fn main() {
    let foo = MyStruct {};

    public();
}
