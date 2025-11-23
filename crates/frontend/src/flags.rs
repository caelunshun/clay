use std::{env, sync::OnceLock};

pub fn should_print_diagnostic_origins() -> bool {
    static CACHE: OnceLock<bool> = OnceLock::new();

    *CACHE.get_or_init(|| env::var("FIR_PRINT_DIAG_ORIGINS").is_ok())
}
