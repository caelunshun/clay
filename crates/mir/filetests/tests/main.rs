mod harnesses {
    use fir_mir::{formatter::format_context, module::Context, parser::parse_mir};
    use pretty_assertions::assert_eq;
    use salsa::{Database, DatabaseImpl};

    #[salsa::input(debug)]
    struct Input {
        src: &'static str,
    }

    #[salsa::tracked]
    fn parse<'db>(db: &'db dyn Database, input: Input) -> Context<'db> {
        parse_mir(db, input.src(db)).expect("failed to parse")
    }

    /// Verifies that parsing a module succeeds, and that
    /// roundtripping produces the expected output.
    pub fn parser_roundtrip(input: &'static str, expected: &'static str) {
        let db = DatabaseImpl::new();
        let input = Input::new(&db, input);
        let input = parse(&db, input);

        let roundtripped = format_context(&db, input).to_string();

        assert_eq!(roundtripped.trim(), expected.trim());
    }
}

include!(concat!(env!("OUT_DIR"), "/generated.rs"));
