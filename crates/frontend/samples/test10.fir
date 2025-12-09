pub struct u32;

pub enum Demo {
    Foo(u32),
    Bar(u32),
}

pub use Demo::*;

fn main(v: u32) {
    let Foo(a) | Bar(a) = 1;

    let mut foo = 0;

    foo = "meow";
}
