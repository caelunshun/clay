fn main() {
    meow::<()>;

    let foo = true;

    if foo {
        foo
    } else {
        ()
    }
}

trait Waow {}

fn meow<T: Waow>() {}
