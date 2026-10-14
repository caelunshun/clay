use std::{env, sync::OnceLock};

pub fn should_print_diagnostic_origins() -> bool {
    static CACHE: OnceLock<bool> = OnceLock::new();

    *CACHE.get_or_init(|| env::var("CLAY_PRINT_DIAG_ORIGINS").is_ok())
}

pub fn should_print_parse_expect_success() -> bool {
    static CACHE: OnceLock<bool> = OnceLock::new();

    *CACHE.get_or_init(|| env::var("CLAY_PRINT_PARSE_EXPECT_SUCCESS").is_ok())
}

pub fn should_print_mir_scopes() -> bool {
    static CACHE: OnceLock<bool> = OnceLock::new();

    *CACHE.get_or_init(|| env::var("CLAY_PRINT_MIR_SCOPES").is_ok())
}
