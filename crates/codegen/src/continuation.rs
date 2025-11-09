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

use crate::strand::InternedStrand;
use mir::{BasicBlockId, InstrData, TypeArgs};
use salsa::Database;
use std::{alloc::Layout, collections::BTreeSet};

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
    layout: Layout,
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
/// by a strand.
#[salsa::tracked]
pub fn get_strand_ret_mechanism<'db>(
    db: &'db dyn Database,
    mir_cx: mir::Context<'db>,
    strand: InternedStrand<'db>,
    type_args: TypeArgs<'db>,
) -> StrandRetMechanism {
    let strand = strand.data(db);
    let func_data = strand.root_atom().func().data(db, mir_cx);

    if strand.root_atom().entry() == func_data.entry_block {
        return StrandRetMechanism::Function;
    }

    let mut variants: Vec<ContVariant> = Vec::new();

    let mut stack = vec![strand.root_atom().entry()];
    let mut visited = BTreeSet::new();
    visited.insert(strand.root_atom().entry());

    while let Some(current_id) = stack.pop() {
        if matches!(
            func_data.basic_blocks[current_id].instrs.last().unwrap(),
            InstrData::Return { .. }
        ) {
            if !variants
                .iter()
                .any(|v| matches!(v.destination(), Destination::Return { .. }))
            {
                let tag = u32::try_from(variants.len()).unwrap();
                let return_type_layout = crate::layout::layout_of(
                    db,
                    mir_cx,
                    func_data.header.return_type,
                    type_args.clone(),
                );
                let (variant_layout, return_val_offset) =
                    Layout::new::<u32>().extend(return_type_layout).unwrap();

                variants.push(ContVariant {
                    tag,
                    layout: variant_layout,
                    destination: Destination::Return {
                        return_val_offset: return_val_offset.try_into().unwrap(),
                    },
                });
            }

            continue;
        }

        func_data.visit_block_successors(current_id, |succ| {
            if !strand.root_atom().contains_bb(succ) {
                if variants.iter().any(
                    |v| matches!(v.destination(), Destination::BasicBlock { bb, .. } if *bb == succ),
                ) {
                    return;
                }

                let tag = u32::try_from(variants.len()).unwrap();
                let mut arg_offsets = Vec::new();
                let mut variant_layout = Layout::new::<u32>();
                for param_val in func_data.basic_blocks[succ]
                    .params
                    .as_slice(&func_data.val_lists)
                {
                    let param_type = func_data.vals[*param_val].typ;
                    let param_layout =
                        crate::layout::layout_of(db, mir_cx, param_type, type_args.clone());
                    let (new_variant_layout, arg_offset) =
                        variant_layout.extend(param_layout).unwrap();
                    arg_offsets.push(arg_offset.try_into().unwrap());
                    variant_layout = new_variant_layout;
                }

                variants.push(ContVariant {
                    tag,
                    layout: variant_layout,
                    destination: Destination::BasicBlock {
                        bb: succ,
                        arg_offsets,
                    },
                });
            } else if visited.insert(succ) {
                stack.push(succ);
            }
        });
    }

    if variants
        .iter()
        .all(|v| matches!(v.destination(), Destination::Return { .. }))
    {
        return StrandRetMechanism::TailCall;
    }

    let mut overall_layout = Layout::new::<()>();
    for variant in &variants {
        overall_layout = Layout::from_size_align(
            overall_layout.size().max(variant.layout.size()),
            overall_layout.align().max(variant.layout.align()),
        )
        .unwrap();
    }

    StrandRetMechanism::Cont(ContLayout {
        overall: overall_layout,
        tag_offset: 0,
        variants,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::strand::{GBasicBlockId, Strand};
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
            get_strand_ret_mechanism(
                db,
                mir_cx,
                InternedStrand::new(db, Strand::of_single_block(gbb)),
                TypeArgs::default()
            ),
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
            bb: func.data(db).block_by_name("block1").unwrap(),
        };

        assert_eq!(
            get_strand_ret_mechanism(
                db,
                mir_cx,
                InternedStrand::new(db, Strand::of_single_block(gbb)),
                TypeArgs::default()
            ),
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

        let blocks = [
            func.data(db).block_by_name("block1").unwrap(),
            func.data(db).block_by_name("block2").unwrap(),
            func.data(db).block_by_name("block3").unwrap(),
        ];

        let StrandRetMechanism::Cont(cont) = get_strand_ret_mechanism(
            db,
            mir_cx,
            InternedStrand::new(db, Strand::of_single_func(func_id, blocks[0], blocks)),
            TypeArgs::default(),
        ) else {
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
