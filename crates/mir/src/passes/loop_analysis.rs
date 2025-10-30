use crate::{BasicBlockId, Context, Func};
use compact_str::format_compact;
use cranelift_entity::{EntityRef, EntitySet, SecondaryMap};
use fir_core::sexpr::{self, SExpr, list, symbol};
use salsa::Database;

/// Analysis of the control-flow graph of a Func to determine the natural loops
/// of a function.
#[salsa::tracked(debug)]
pub struct LoopAnalysis<'db> {
    pub func: Func<'db>,
    #[tracked]
    #[returns(ref)]
    pub loops: Vec<Loop>,
}

/// A natural loop.
///
/// This is a maximal set of basic blocks such that there is a single
/// header that dominates all other blocks in the loop,
/// one or more blocks that have a back-edge to the header,
/// and all other blocks dominate the back-edges (but post-dominate
/// the header). Not all cyclic control flow structures can be represented
/// here, but such structures don't appear in real programs that don't use goto,
/// so they are simply not counted as loops.
#[derive(Debug, Clone, PartialEq, Eq, salsa::Update)]
pub struct Loop {
    pub header: BasicBlockId,
    /// Set of all blocks in the loop, including the header.
    pub parts: EntitySet<BasicBlockId>,
    /// 0 for top-level loops, increasing by 1
    /// for each nested level of loops.
    pub depth: u32,
}

impl<'db> LoopAnalysis<'db> {
    /// Produces an SExpr representation useful
    /// for testing.
    pub fn to_sexpr(&self, db: &'db dyn Database, _cx: Context<'db>) -> SExpr {
        let func = self.func(db).data(db);

        let mut loops = Vec::new();
        for loop_ in self.loops(db) {
            let mut loop_expr = vec![symbol("loop")];

            loop_expr.push(list([
                symbol("header"),
                symbol(
                    func.basic_blocks[loop_.header]
                        .name
                        .clone()
                        .unwrap_or_else(|| format_compact!("block{}", loop_.header.index())),
                ),
            ]));

            loop_expr.push(list([symbol("depth"), sexpr::int(loop_.depth as _)]));

            let mut parts = Vec::new();
            for part in loop_.parts.iter() {
                let name = func.basic_blocks[part]
                    .name
                    .clone()
                    .unwrap_or_else(|| format_compact!("block{}", part.index()));
                parts.push(name);
            }

            loop_expr.push(list([symbol("parts"), list(parts.into_iter().map(symbol))]));

            loops.push(list(loop_expr));
        }

        loops.insert(0, symbol("loops"));
        list(loops)
    }
}

/// Performs loop analysis on the given function.
/// The function must already be in SSA form.
#[salsa::tracked]
pub fn do_loop_analysis<'db>(db: &'db dyn Database, func: Func<'db>) -> LoopAnalysis<'db> {
    let func_data = func.data(db);
    let ancestors = func_data.compute_acyclic_ancestors();

    // First, we'll find all back-edges, which gives us a set
    // of candidate headers.
    // Then, for each candidate header and its back-edges, we'll
    // calculate the "part" blocks. This step can fail if
    // any of these blocks can be jumped to from outside the loop;
    // if so, we discard this loop.
    // Finally, we calculate nesting levels.

    let mut back_edges: SecondaryMap<BasicBlockId, Vec<BasicBlockId>> = SecondaryMap::default();

    for block in func_data.basic_blocks.keys() {
        func_data.visit_block_successors(block, |predecessor| {
            if ancestors[block].contains(predecessor) {
                back_edges[predecessor].push(block);
            }
        });
    }

    let mut loops = Vec::new();

    for (candidate_header, back_edges) in back_edges.iter() {
        if back_edges.is_empty() {
            continue;
        }

        let mut stack = back_edges.clone();
        let mut parts = EntitySet::new();
        parts.extend(back_edges.iter().copied());
        parts.insert(candidate_header);

        while let Some(current) = stack.pop() {
            if current != candidate_header {
                func_data.visit_block_predecessors(current, |predecessor| {
                    if parts.insert(predecessor) {
                        stack.push(predecessor);
                    }
                });
            }
        }

        // Verify no predecessors outside the loop, except for the header
        let mut valid = true;
        for part in parts.iter() {
            if part != candidate_header {
                func_data.visit_block_predecessors(part, |pred| {
                    if !parts.contains(pred) {
                        valid = false;
                    }
                });
            }
        }

        if valid {
            loops.push(Loop {
                header: candidate_header,
                parts,
                depth: 0,
            });
        }
    }

    LoopAnalysis::new(db, func, loops)
}
