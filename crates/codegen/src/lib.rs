//! Translation layer from MIR to a low-level codegen backend.
//!
//! This layer is responsible for lowering MIR instructions to
//! low-level, runtime-aware instructions, for scalar replacement
//! of aggregates, and for monomorphization.
//! It can be seen as building a "low-level" intermediate
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
//!
//! # Runtime integration
//! This translation layer naturally requires awareness of runtime-specific details:
//! * There is a predefined set of "intrinsic host calls" used for routines like memory allocation,
//!   GC safepoints, and slow paths for bufref mutations. The absolute addresses of these routines
//!   are provided by the caller.
//! * High-level MIR types like bufrefs and futexes
//!   use representations given in the runtime docs.
//! * Managed references are implemented with pointer tagging
//!   as described in the runtime docs. In particular,
//!   the upper TAGGED_REFERENCE_RESERVED_BITS
//!   bits of a pointer must be masked out
//!   before using it for memory operations.
//! * We pass around a thread-local VM context pointer to every compiled strand as the first
//!   argument. We also pass this pointer as the first argument to all host calls.
//!   The offsets of relevant fields relative to this pointer are passed by the caller.
//!   Some of these fields include:
//!     * An atomic boolean `request_pause` which, if set, signals the current thread that it should
//!       push all of its live values onto the stack and then invoke the `safepoint` intrinsic host call.
//!       This functionality is used for stop-the-world GC phases as well as for code updates
//!       when hot reloading.
//!       We check the value of this field at the start of each strand and loop iteration.
//!     * A pointer to the global VM context, which contains state shared between threads
//!       (but expensive to mutate due to cache line migration).
//!       The pointer value is read-only, so backends can perform redundant load elimination on it.
//!       The global context contains:
//!         * A pointer to the global offset table (GOT), which stores the addresses
//!           of compiled strands.
//! * On x86_64, all functions use the SystemV calling convention, even on Windows.
//! * Guest function and strand calls go through the GOT stored in the global VM context.
//! * Optionally, the code generator can insert profile collection instructions.
//!   In the runtime, profile data consists of a table storing a countdown for
//!   each basic block. When the countdown reaches zero, the block_countdown_reached
//!   host call is invoked, possibly triggering an upgraded compilation of the block
//!   and its neighbors.
//!   The code generator emits an instruction at the top of each basic block
//!   to decrement this value. The address of the countdown for each block is provided
//!   by the caller.
//! * Optionally, the code generator can emit code
//!   that supports a form of on-stack replacement (OSR).
//!   OSR is used to upgrade the optimization level of a function while it is executing,
//!   which is often needed for long-running loops.
//!   OSR-enabled code will, at the start of each loop iteration of every loop in the strand,
//!   check a boolean flag (address provided by the caller). If the flag is true, then we
//!   build a data structure on the stack containing all the arguments to the loop iteration,
//!   and finally pass this to the on_stack_replace host call.
//! * We require 64- and 128-bit atomics for various operations. If not supported
//!   by the ISA, then we polyfill these using a global hash table of spinlocks.
//!   The address of this `spinlock_table` is provided by the caller.

#![cfg_attr(target_arch = "riscv64", feature(stdarch_riscv_feature_detection))]

extern crate fir_mir as mir;

pub mod backend;
pub mod compiled_strand;
pub mod intrinsic;
pub mod isa;
pub mod layout;
pub mod lowering;
pub mod strand;

