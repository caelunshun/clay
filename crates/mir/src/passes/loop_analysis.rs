use crate::{BasicBlockId, Context, Func};
use compact_str::format_compact;
use cranelift_entity::EntityRef;
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct Loop {
    pub header: BasicBlockId,
    pub parts: Vec<BasicBlockId>,
    /// 0 for top-level loops, increasing by 1
    /// for each nested level of loops.
    pub depth: u32,
}

impl<'db> LoopAnalysis<'db> {
    /// Produces an SExpr representation useful
    /// for testing.
    pub fn to_sexpr(&self, db: &'db dyn Database, cx: Context<'db>) -> SExpr {
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
            for part in &loop_.parts {
                let name = func.basic_blocks[*part]
                    .name
                    .clone()
                    .unwrap_or_else(|| format_compact!("block{}", part.index()));
                parts.push(name);
            }
            parts.sort_unstable();

            loop_expr.push(list([symbol("parts"), list(parts.into_iter().map(symbol))]));

            loops.push(list(loop_expr));
        }

        list([symbol("loops"), list(loops)])
    }
}

#[salsa::tracked]
pub fn do_loop_analysis<'db>(db: &'db dyn Database, func: Func<'db>) -> LoopAnalysis<'db> {
    todo!()
}
