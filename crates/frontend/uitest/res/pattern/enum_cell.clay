enum Foo {
    Bar(u32),
    Baz,
}

fn rejected_1(foo: @mut Foo) {
    match foo {
        // FIXME: by-ref shouldn't be available for unlocked enums.
        Foo::Bar(ref v) => {
            let v: @u32 = v;
            *foo = Foo::Baz;
            *v;
        }
        Foo::Baz => {}
    }
}

fn rejected_2(mut foo: Foo) {
    match foo {
        // FIXME: by-ref shouldn't be available for unlocked enums.
        Foo::Bar(ref v) => {
            let v: @u32 = v;
            foo = Foo::Baz;
            *v;
        }
        Foo::Baz => {}
    }
}

fn accepted_1(foo: @mut Foo) {
    match foo {
        // Copying values is okay.
        Foo::Bar(v) => {
            let _: u32 = v;
            *foo = Foo::Baz;
        }
        Foo::Baz => {}
    }
}

fn accepted_2(foo: @EnumCell<Foo>) {
    match foo.acquire() {
        // Borrowing from a guard is okay.
        Foo::Bar(ref v) => {
            let _: &u32 = v;
        }
        Foo::Baz => {}
    }
}

fn rejected_3(foo: @EnumCell<Foo>) {
    match foo.acquire() {
        Foo::Bar(ref v) => {
            // FIXME: guards aren't locked forever.
            let _: @u32 = v;
        }
        Foo::Baz => {}
    }
}

fn rejected_4(foo: @EnumCell<Foo>) {
    match foo.acquire() {
        Foo::Bar(ref mut v) => {
            // FIXME: guards have mutability
            let _: &mut u32 = v;
        }
        Foo::Baz => {}
    }
}

fn accepted_4(foo: @EnumCell<Foo>) {
    match foo.acquire_mut() {
        Foo::Bar(ref mut v) => {
            let _: &mut u32 = v;
        }
        Foo::Baz => {}
    }
}

fn rejected_5(foo: @mut EnumCell<Foo>) {
    match foo.acquire() {
        Foo::Bar(ref v) => {
            let v: &u32 = v;

            // FIXME: `EnumCell`s are not `StructurallyFixed`
            *foo = EnumCell::new(Foo::Baz);
            *v;
        }
        Foo::Baz => {}
    }
}
