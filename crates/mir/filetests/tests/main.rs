mod harnesses {
    use fir_core::sexpr::SExpr;
    use fir_mir::{
        Func,
        formatter::format_context,
        module::{Context, ContextBuilder},
        parser::parse_mir,
        passes, validation,
    };
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

    #[salsa::tracked]
    fn make_ssa<'db>(db: &'db dyn Database, cx: Context<'db>) -> Context<'db> {
        let mut ssa_cx = cx.data(db).clone();
        for func in ssa_cx.funcs.values_mut() {
            let ssa_func = passes::ssa::make_ssa(db, func.data(db));
            *func = Func::new(db, ssa_func);
        }
        Context::new(db, ssa_cx)
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
                if validation::typecheck::verify_instr_types(db, cx, func.data(db)).is_ok() {
                    panic!(
                        "typecheck validation succeeded on function '{}', but was expected to fail",
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

    /// Verifies that cfg_integrity_validation fails on the given module.
    pub fn cfg_integrity_validation_fails(input_str: &'static str) {
        with_parsed_context(input_str, |db, cx| {
            for func in cx.data(db).funcs.values() {
                if validation::cfg_integrity::verify_cfg_integrity(func.data(db)).is_ok() {
                    panic!(
                        "cfg_integrity check succeeded for function '{}', but was expected to fail",
                        func.data(db).header.name
                    );
                }
            }
        });
    }

    /// Verifies that SSA validation passes on the given module.
    pub fn ssa_validation_succeeds(input_str: &'static str) {
        with_parsed_context(input_str, |db, cx| {
            for func in cx.data(db).funcs.values() {
                validation::ssa::verify_ssa(func.data(db)).unwrap_or_else(|e| {
                    panic!(
                        "SSA validation failed for function '{}': {e:?}",
                        func.data(db).header.name
                    );
                });
            }
        });
    }

    /// Verifies that SSA validation fails on the given module.
    pub fn ssa_validation_fails(input_str: &'static str) {
        with_parsed_context(input_str, |db, cx| {
            for func in cx.data(db).funcs.values() {
                if validation::ssa::verify_ssa(func.data(db)).is_ok() {
                    panic!(
                        "SSA validation succeeded for function '{}', but was expected to fail",
                        func.data(db).header.name
                    );
                }
            }
        });
    }

    /// Applies the SSA transformer to the module
    /// and compares the resulting MIR against
    /// the expected SSA MIR.
    pub fn ssa_construction_matches_expected(input: &'static str, expected: &'static str) {
        with_parsed_context(input, |db, cx| {
            let ssa_cx = make_ssa(db, cx);
            let formatted_module = format_context(db, ssa_cx).to_string();
            let expected_module_normalized = SExpr::parse(expected).unwrap().to_string();
            assert_eq!(formatted_module, expected_module_normalized);
        });
    }
}

include!(concat!(env!("OUT_DIR"), "/generated.rs"));
