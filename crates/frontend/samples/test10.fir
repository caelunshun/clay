pub struct u32;

pub enum Demo {
    Foo(u32),
    Bar(u32),
    Baz {},
}

pub use Demo::*;

fn main(v: u32) {
    let Foo((-1, a)) | Bar(a) = 1;

    [v, .., v, .., v] = [1, 2, 3];

    let mut foo = 0;

    foo = "meow";

    match foo {
        -0 => 1,
        -1..-1 => {},
        'a'..='z' => {},
        "meow" => {},
    }
}
