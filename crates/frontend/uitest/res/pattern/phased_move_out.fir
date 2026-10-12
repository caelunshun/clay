enum Foo {
    Bar(NoCopy),
}

struct NoCopy;

fn should_accept(v: Foo) {
    match v {
        Foo::Bar(taken) if false => {}
        Foo::Bar(taken) => {
            consume(taken);
        }
    }
}

fn should_reject(v: Foo) {
    match v {
        // FIXME: First case should be denied.
        Foo::Bar(taken) if { consume(taken); false } => {}
        Foo::Bar(taken) => {
            consume(taken);
        }
    }
}

fn consume(v: NoCopy) {}
