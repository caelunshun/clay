mod accepted {
    mod ex1 {
        struct Foo<'a, T: &longer 'a>(Bar<'a, T>);

        struct Bar<'a: &shorter T, T>;
    }

    mod ex2 {
        struct Foo<'a: &shorter T, T>(Bar<'a, T>);

        struct Bar<'a, T: &longer 'a>;
    }

    mod ex3 {
        struct Foo<'a, T: &shorter 'a>(Bar<'a, T>);

        struct Bar<'a: &longer T, T>;
    }

    mod ex4 {
        struct Foo<'a: &longer T, T>(Bar<'a, T>);

        struct Bar<'a, T: &shorter 'a>;
    }
}

mod rejected {
    mod ex1 {
        struct Foo<'a, T: &longer 'a>(Bar<'a, T>);

        struct Bar<'a: &longer T, T>;
    }

    mod ex2 {
        struct Foo<'a: &shorter T, T>(Bar<'a, T>);

        struct Bar<'a, T: &shorter 'a>;
    }

    mod ex3 {
        struct Foo<'a, T: &shorter 'a>(Bar<'a, T>);

        struct Bar<'a: &shorter T, T>;
    }

    mod ex4 {
        struct Foo<'a: &longer T, T>(Bar<'a, T>);

        struct Bar<'a, T: &longer 'a>;
    }
}
