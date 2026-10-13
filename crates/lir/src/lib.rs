//! Low-level Intermediate Representation, the format ingested by the runtime.

#![allow(deprecated)] // index_vec macro

pub mod arena;
pub mod brick;
pub mod func;
pub mod soup;
pub mod subst_ty;
pub mod trait_family;
pub mod ty;
pub mod adt_family;
