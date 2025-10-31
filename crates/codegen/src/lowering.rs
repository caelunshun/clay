//! Lowering of MIR strands to the codegen backend.

use crate::{
    backend::{self, CodeBuilder, CodegenBackend},
    compiled_strand::CompiledStrand,
    isa::Isa,
    lowering::{context::LoweringCx, env::Env},
    strand::{GBasicBlockId, Strand},
};
use bumpalo::Bump;
use fir_core::HashMap;
use salsa::Database;
use std::cell::{LazyCell, RefCell};

mod compound_val;
mod context;
pub mod env;

pub fn compile_strand<'db, B>(
    db: &'db dyn Database,
    mir_cx: mir::Context<'db>,
    backend: &B,
    env: &dyn Env,
    strand: &Strand,
) -> CompiledStrand
where
    B: CodegenBackend,
{
    thread_local! {
        static LOWERING_CX: LazyCell<RefCell<LoweringCx>> = LazyCell::new(Default::default);
    }

    LOWERING_CX.with(|cx_cell| {
        let mut cx = cx_cell.borrow_mut();

        let mut lowerer = Lowerer {
            db,
            mir_cx,
            env,
            isa: backend.isa(),
            backend: backend.make_code_builder(&cx.bump, todo!()),
            strand,
            bump: &cx.bump,
            bb_mapping: &mut cx.bb_mapping,
        };

        cx.reset();

        todo!()
    })
}

struct Lowerer<'db, 'a, B> {
    db: &'db dyn Database,
    mir_cx: mir::Context<'db>,
    env: &'a dyn Env,
    isa: &'a Isa,
    backend: B,
    strand: &'a Strand,
    bump: &'a Bump,
    bb_mapping: &'a mut HashMap<GBasicBlockId, backend::BasicBlockId>,
}

impl<'db, 'a, B> Lowerer<'db, 'a, B>
where
    B: CodeBuilder<'a>,
{
    fn lower_bb(&mut self, id: GBasicBlockId, bb: &'db mir::BasicBlock<'db>) {
        self.backend.switch_to_block(self.bb_mapping[&id]);

        todo!()
    }
}
