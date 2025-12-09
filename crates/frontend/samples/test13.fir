fn main() {
    let [a, b, c | d | e | f, g | () | () | ()] = [1, 2, 3, 4];

    if
        let foo = a
        && let bar = foo.bar
        && bar.baz
        || let maz = 3
        && let faz = 5
        || foo
        && let uh_oh = 6
    {
        bar.maz();
    }

    let Meow { mut a, b } = ();
}

pub struct Meow { a: () }
