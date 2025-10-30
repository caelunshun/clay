//! Translation layer from MIR to a low-level codegen backend.
//!
//! This layer is responsible for lowering MIR instructions to
//! low-level, runtime-aware instructions, and for scalar replacement
//! of aggregates. It can be seen as building a "low-level" intermediate
//! representation (LIR), except this IR is never explicitly materialized.
//! Instead, we make method calls for each lowered instruction
//! to a pluggable codegen backend, which can choose to either translate
//! to a backend IR (cranelift or LLVM) or generate machine code on the fly (baseline
//! singlepass compiler).
//!
//! The unit of compilation is the _strand_. A strand is a collection of MIR basic blocks,
//! _not required to all reside in the same MIR function_, whose predecessors are all
//! inside the strand (except for the entry block, which can have outside predecessors).
//! This representation can be seen
//! as a form of inlining, where basic blocks from multiple functions can be combined
//! into a single strand for compilation. The JIT layer in the runtime chooses how
//! to partition blocks into strands using profile-guided heuristics.
