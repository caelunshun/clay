//! Defines the MIR structure.

pub mod adt;
pub mod constant;
pub mod context;
pub mod func;
pub mod instr;
pub mod trait_;
pub mod typ;
pub mod type_param;

pub use adt::*;
pub use constant::*;
pub use context::*;
pub use func::*;
pub use trait_::*;
pub use typ::*;
pub use type_param::*;
