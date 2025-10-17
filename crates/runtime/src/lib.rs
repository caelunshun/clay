mod engine;
mod error;
mod gc;
mod gc_impl;
mod interpreter;
mod ptr;
mod type_registry;
mod value;

extern crate fir_bytecode as bytecode;

pub use engine::{Engine, Func, Instance, Module};
pub use error::Error;
pub use value::Value;
