//! We use continuations to direct control flow from a child strand
//! back to its caller, in cases where the strand entry point is not
//! the function entry point.
//!
//! For instance, consider a function that looks like the following pseudocode:
//! ```text
//! fn foo() -> int {
//!     let x = /* calculation.... */;
//!     loop {
//!         // ....
//!         if cond1 {
//!             break;
//!         }
//!         if cond2 {
//!             return 10;
//!         }
//!     }
//!     return x;
//! }
//! ```
//!
//! Now suppose the loop has been identified as hot, so it (but not
//! the outer function body) is being
//! compiled as a strand. Now, the updated function body will, upon entering
//! the loop, make a call to this newly compiled strand. When the strand
//! returns, it needs to tell the function body which control flow was
//! reached - in this case, whether the break statement (corresponding to a
//! jump to the block containing `return x`) or the `return` statement was reached.
//! We encode this through _continuations_. Every strand whose entrypoint is not a function
//! entrypoint returns a continuation, effectively a tagged union whose variants correspond
//! to destination blocks and their arguments.
//!
//! As a special case, if a strand does not jump to any outer basic blocks
//! but only returns from the current function, then it does not need to return
//! a continuation; instead, it can be tail-called and then return directly.
//! In the example above, this would occur if the loop did not contain a break statement.
