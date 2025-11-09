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

use crate::strand::GBasicBlockId;
use mir::BasicBlockId;
use salsa::Database;
use std::alloc::Layout;

/// Layout of a continuation returned by a strand.
///
/// The tag is 32 bits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContLayout {
    overall: Layout,
    tag_offset: u32,
    variants: Vec<ContVariant>,
}

impl ContLayout {
    pub fn overall_layout(&self) -> Layout {
        self.overall
    }

    pub fn tag_offset(&self) -> u32 {
        self.tag_offset
    }

    pub fn variants(&self) -> impl Iterator<Item = &ContVariant> {
        self.variants.iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContVariant {
    tag: u32,
    destination: Destination,
}

impl ContVariant {
    pub fn tag(&self) -> u32 {
        self.tag
    }

    pub fn destination(&self) -> &Destination {
        &self.destination
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Destination {
    BasicBlock {
        bb: BasicBlockId,
        arg_offsets: Vec<u32>,
    },
    Return {
        return_val_offset: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StrandRetMechanism {
    /// Strand's entry point is a function entry point,
    /// so it does not need to return a continuation.
    Function,
    /// Strand only returns from the current function and
    /// cannot jump to any outside block inside the function,
    /// so it can be tail-called.
    TailCall,
    /// Strand needs to return a continuation.
    Cont(ContLayout),
}

/// Computes the continuation layout that must be returned
/// by a strand whose entry point is the given block.
#[salsa::tracked]
pub fn get_strand_ret_mechanism<'db>(
    db: &'db dyn Database,
    mir_cx: mir::Context<'db>,
    strand_entrypoint: GBasicBlockId,
) -> StrandRetMechanism {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use mir::parser::parse_mir;
    use salsa::DatabaseImpl;

    #[salsa::input]
    struct Input {
        src: &'static str,
    }

    #[salsa::tracked]
    fn must_parse_mir<'db>(db: &'db dyn Database, input: Input) -> mir::Context<'db> {
        parse_mir(db, input.src(db)).unwrap()
    }

    #[test]
    fn function_return_mechanism() {
        let mir = r#"
        (mir
            (func foo
                (return_type int)
                (entry block0)
                (block block0
                    (constant x (0))
                    (return (x)))))
        "#;
        let db = &DatabaseImpl::default();
        let mir_cx = must_parse_mir(db, Input::new(db, mir));

        let (func_id, func) = mir_cx.data(db).funcs.iter().next().unwrap();
        let gbb = GBasicBlockId {
            func: func_id,
            bb: func.data(db).entry_block,
        };

        assert_eq!(
            get_strand_ret_mechanism(db, mir_cx, gbb),
            StrandRetMechanism::Function
        );
    }

    #[test]
    fn tailcall_return_mechanism() {
        let mir = r#"
        (mir
            (func foo
                (return_type int)
                (entry block0)
                (block block0
                    (jump (block1 ())))
                (block block1
                    (constant x (0))
                    (return (x)))))
        "#;
        let db = &DatabaseImpl::default();
        let mir_cx = must_parse_mir(db, Input::new(db, mir));

        let (func_id, func) = mir_cx.data(db).funcs.iter().next().unwrap();
        let gbb = GBasicBlockId {
            func: func_id,
            bb: func
                .data(db)
                .basic_blocks
                .iter()
                .find_map(|(bb, data)| {
                    if data.name.as_deref() == Some("block1") {
                        Some(bb)
                    } else {
                        None
                    }
                })
                .unwrap(),
        };

        assert_eq!(
            get_strand_ret_mechanism(db, mir_cx, gbb),
            StrandRetMechanism::TailCall
        );
    }

    #[test]
    fn cont_return_mechanism() {
        let mir = r#"
        (mir
            (func foo
                (return_type int)
                (entry block0)
                (block block0
                    (jump (block1 ())))
                (block block1
                    (constant cond (false))
                    (branch
                        (cond
                            (true block2 ())
                            (false block3 ()))))
                (block block2
                    (constant x (0))
                    (return (x)))
                (block block3
                    (jump (block0 ())))))
        "#;
        let db = &DatabaseImpl::default();
        let mir_cx = must_parse_mir(db, Input::new(db, mir));

        let (func_id, func) = mir_cx.data(db).funcs.iter().next().unwrap();
        let gbb = GBasicBlockId {
            func: func_id,
            bb: func
                .data(db)
                .basic_blocks
                .iter()
                .find_map(|(bb, data)| {
                    if data.name.as_deref() == Some("block1") {
                        Some(bb)
                    } else {
                        None
                    }
                })
                .unwrap(),
        };

        let StrandRetMechanism::Cont(cont) = get_strand_ret_mechanism(db, mir_cx, gbb) else {
            panic!("not a cont")
        };

        assert_eq!(cont.variants().count(), 2);

        assert!(
            cont.variants()
                .any(|v| matches!(v.destination(), Destination::Return { .. }))
        );
        assert!(
            cont.variants()
                .any(|v| matches!(v.destination(), Destination::BasicBlock {
                    bb,
                    arg_offsets,
                } if *bb == func.data(db).entry_block && arg_offsets.is_empty()))
        );
    }
}
