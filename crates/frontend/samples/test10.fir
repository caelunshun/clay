pub struct u32;

pub enum Demo {
    Foo(u32),
    Bar(u32),
    Baz {},
}

fn main(v: u32) {
    let Demo::Foo((-1, a)) | Demo::Bar(a) = 1;

    let mut foo = 0;

    foo = "meow";

    match foo {
        -0 => 1,
        -1..-1 => {}
        'a'..='Z' => {},
        -1 => {}
        "meow" => {},
    }
}
