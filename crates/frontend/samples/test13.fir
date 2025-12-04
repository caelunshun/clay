fn main() {
    whee::<i32>();

    Woo::<Foo = (), u32>::new::<(), Maz = ()>()
}

struct i32 {}

pub struct Woo<'a> {}

mod u32 {}

pub fn whee() {}
