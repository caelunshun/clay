fn main() {
    let x = 1;
    let y = &x;

    if false {
        x;
        x;
    }

    x;
    y;
}
