mod harnesses {
    use fir_core::sexpr::SExpr;
    use fir_mir::{formatter::format_context, module::Context, parser::parse_mir, validation};
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
    pub fn parser_roundtrip(input_str: &'static str) {
        let db = DatabaseImpl::new();
        let input = Input::new(&db, input_str);
        let input = parse(&db, input);

        let roundtripped = format_context(&db, input).to_string();
        let expected_normalized = SExpr::parse(input_str).unwrap().to_string();

        assert_eq!(roundtripped, expected_normalized);
    }

    /// Verifies that typecheck validation passes on the given module.
    pub fn typecheck_validation_passes(input_str: &'static str) {
        let db = DatabaseImpl::new();
        let input = Input::new(&db, input_str);
        let cx = parse(&db, input);

        for func in cx.data(&db).funcs.values() {
            validation::typecheck::verify_instr_types(&db, cx, func.data(&db)).unwrap_or_else(
                |e| {
                    panic!(
                        "failed typecheck for func '{}': {e:?}",
                        func.data(&db).header.name
                    )
                },
            );
        }
    }
}

include!(concat!(env!("OUT_DIR"), "/generated.rs"));
