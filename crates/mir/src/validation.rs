//! MIR validation passes.
//!
//! These passes are not intended to provide diagnostics
//! directly to users. Instead, they assert invariants required
//! for codegen to be sound. They are used for testing and sanity
//! checks in the compiler.

use std::{fmt::Display, panic::Location};

pub mod cfg_integrity;
pub mod ssa;
pub mod typecheck;
pub mod value_initialization;

#[derive(Debug, Clone)]
pub struct ValidationError(pub String, pub &'static Location<'static>);

impl ValidationError {
    #[track_caller]
    pub fn new(msg: impl Display) -> Self {
        Self(msg.to_string(), Location::caller())
    }
}
