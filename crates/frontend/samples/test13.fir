fn main() {
    Woo::<Foo = (), u32>::new::<(), Maz = ()>()
}

pub struct Woo<'a> {}

mod u32 {}
