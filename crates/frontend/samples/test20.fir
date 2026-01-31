fn main() {
    meow::<()>;

    if true {
        true
    } else {
        ()
    }
}

trait Waow {}

fn meow<T: Waow>() {}
