mod meow {
    pub struct u32 {
        _private: (),
    }

    pub struct i32(pub u32, (), ());

    pub enum Whee {
        Foo(i32),
    }

    fn yay() {
        i32((), ());
    }
}

use meow::*;

pub enum Demo {
    Foo(u32),
    Bar(u32),
    Baz {},
}

pub trait Meow<T: Meow<T>> {}

fn main(v: dyn Meow<()>) {
    let Demo::Foo((-1, a)) | Demo::Bar(a) = 1;

    let mut foo = 0;

    foo = "meow";

    u32 { _private: () };

    i32((), ());

    match foo {
        -0 => 1,
        -1..-1 => {}
        'a'..='Z' => {},
        -1 => {}
        u32 { _private } => (),
        i32((), ..) => {}
        i32((), (), ..) => {}
        i32((), .., ()) => {}
        "meow" => {},
    }
}
