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

    fn with_parsed_context(
        input_str: &'static str,
        callback: impl for<'db> FnOnce(&'db dyn Database, Context<'db>),
    ) {
        let db = DatabaseImpl::new();
        let input = Input::new(&db, input_str);
        let cx = parse(&db, input);
        callback(&db, cx);
    }

    /// Verifies that parsing a module succeeds, and that
    /// roundtripping produces the expected output.
    pub fn parser_roundtrip(input_str: &'static str) {
        with_parsed_context(input_str, |db, cx| {
            let roundtripped = format_context(db, cx).to_string();
            let expected_normalized = SExpr::parse(input_str).unwrap().to_string();

            assert_eq!(roundtripped, expected_normalized);
        });
    }

    /// Verifies that typecheck validation passes on the given module.
    pub fn typecheck_validation_succeeds(input_str: &'static str) {
        with_parsed_context(input_str, |db, cx| {
            for func in cx.data(db).funcs.values() {
                validation::typecheck::verify_instr_types(db, cx, func.data(db)).unwrap_or_else(
                    |e| {
                        panic!(
                            "failed typecheck for func '{}': {e:?}",
                            func.data(db).header.name
                        )
                    },
                );
            }
        });
    }

    /// Verifies that typecheck validation does not pass on the given module.
    pub fn typecheck_validation_fails(input_str: &'static str) {
        with_parsed_context(input_str, |db, cx| {
            for func in cx.data(db).funcs.values() {
                if !validation::typecheck::verify_instr_types(db, cx, func.data(db)).is_err() {
                    panic!(
                        "typecheck validation succeeded on function '{}', but was not expected to succeed",
                        func.data(db).header.name
                    );
                }
            }
        });
    }

    /// Verifies that value_initialization validation passes on the given module.
    pub fn value_initialization_validation_succeeds(input_str: &'static str) {
        with_parsed_context(input_str, |db, cx| {
            for func in cx.data(db).funcs.values() {
                validation::value_initialization::verify_value_initialization(func.data(db))
                    .unwrap_or_else(|e| {
                        panic!(
                            "failed value initialization check for func '{}': {e:?}",
                            func.data(db).header.name
                        )
                    });
            }
        });
    }

    /// Verifies that cfg_integrity_validation succeeds on the given module.
    pub fn cfg_integrity_validation_succeeds(input_str: &'static str) {
        with_parsed_context(input_str, |db, cx| {
            for func in cx.data(db).funcs.values() {
                validation::cfg_integrity::verify_cfg_integrity(func.data(db)).unwrap_or_else(
                    |e| {
                        panic!(
                            "failed control flow integrity check for func '{}': {e:?}",
                            func.data(db).header.name
                        )
                    },
                );
            }
        });
    }
}

include!(concat!(env!("OUT_DIR"), "/generated.rs"));
