//! Lowering of MIR strands to the codegen backend.

use crate::{
    backend::{self, CodeBuilder, CodegenBackend, Signature, ValTy},
    compiled_strand::CompiledStrand,
    isa::Isa,
    lowering::{
        compound_val::{scalarize_type, scalarize_types},
        context::LoweringCx,
        env::Env,
    },
    strand::{GBasicBlockId, Strand},
};
use bumpalo::Bump;
use fir_core::HashMap;
use mir::FuncId;
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

        let entry_block = strand.entry_block().resolve(db, mir_cx);
        let entry_block_func = strand.entry_block().func.resolve(db, mir_cx).data(db);

        let sig = Signature::new(
            scalarize_types(
                db,
                mir_cx,
                entry_block
                    .params
                    .as_slice(&entry_block_func.val_lists)
                    .iter()
                    .map(|val_id| entry_block_func.vals[*val_id].typ),
                &cx.bump,
            ),
            scalarize_type(db, mir_cx, entry_block_func.header.return_type, &cx.bump),
        );

        {
            let mut lowerer = Lowerer {
                db,
                mir_cx,
                env,
                isa: backend.isa(),
                backend: backend.make_code_builder(&cx.bump, sig),
                strand,
                bump: &cx.bump,
                bb_mapping: HashMap::new_in(&cx.bump),
            };
        }

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
    bb_mapping: HashMap<BbInstance<'a>, backend::BasicBlockId, &'a Bump>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct BbInstance<'bump> {
    bb: GBasicBlockId,
    call_stack: &'bump [FuncId],
}

impl<'db, 'a, B> Lowerer<'db, 'a, B>
where
    B: CodeBuilder<'a>,
{
    fn lower_bb(&mut self, instance: BbInstance<'a>, bb: &'db mir::BasicBlock<'db>) {
        self.backend.switch_to_block(self.bb_mapping[&instance]);

        for instr in &bb.instrs {
            
        }

        todo!()
    }
}
