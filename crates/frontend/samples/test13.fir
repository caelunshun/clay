fn main() {
    let [a, b, c | d | e | f, g | () | () | ()] = [1, 2, 3, 4];

    if let foo = a && let bar = foo.bar && bar.baz {
        bar.maz();
    }
}
