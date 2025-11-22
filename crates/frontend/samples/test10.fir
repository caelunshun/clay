pub enum Whee<T> {
    Foo(T, (T, T)),
    Bar,
    Baz {},
    Maz { foo: u32, bar: i32 },
}

pub struct Woo<'a, T> {
    pub foo: &'a T,
    bar: (),
}

pub struct Waz(pub u32, pub (), pub(crate) ());

pub struct Faz;

pub fn fizz_buzz(limit: Option<u32>) {
    let mut sb = String::new();

    let range = match limit {
        Some(v) => (0..v).as::<dyn Iterator<Item = u32>>,
        None => (0..).as::<dyn Iterator<Item = u32>>,
    };

    foo.bar::<u32>();

    (foo, bar, Foo { a, b, .. }, _) = baz;

    let foo = (
        Faz,
        Woo { foo, bar: () },
        Whee::Bar,
        Whee::Maz { foo: 1, bar: 2 },
    );

    for i in range {
        let mut special = false;

        if i % 3 == 0 {
            sb.push_str("fizz");
            special |= true;
        }

        if i % 5 == 0 {
            sb.push_str("buzz");
            special |= true;
        }

        if !special {
            sb.push_fmt(format_args("{}", [i]));
        }

        sb.push_char('\n');
        print(&sb);
        sb.clear();
    }
}
