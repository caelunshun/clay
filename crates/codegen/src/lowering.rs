//! Lowering of MIR strands to the codegen backend.

use crate::{
    backend::{self, CodeBuilder, CodegenBackend, IntBitness, Signature, ValTy},
    compiled_strand::CompiledStrand,
    isa::Isa,
    lowering::{
        compound_val::{Compound, scalarize_type, scalarize_types},
        context::LoweringCx,
        env::Env,
    },
    strand::{GBasicBlockId, Strand},
};
use bumpalo::Bump;
use fir_core::HashMap;
use mir::{FuncData, FuncId};
use salsa::Database;
use std::{
    cell::{LazyCell, RefCell},
    iter,
};

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

        let entry_block = strand.entry().resolve(db, mir_cx);
        let entry_block_func = strand.entry().func.resolve(db, mir_cx).data(db);

        let sig = sig_for_strand(db, mir_cx, &cx, strand.entry());

        {
            let mut lowerer = Lowerer {
                db,
                mir_cx,
                env,
                isa: backend.isa(),
                backend: backend.make_code_builder(&cx.bump, sig),
                strand,
                bump: &cx.bump,
                bb_map: HashMap::new_in(&cx.bump),
                val_map: HashMap::new_in(&cx.bump),
                current_bb: BbInstance {
                    bb: strand.entry(),
                    call_stack: &[],
                },
                current_func: entry_block_func,
            };
        }

        cx.reset();

        todo!()
    })
}

fn does_strand_return_continuation<'db>(
    db: &'db dyn Database,
    mir_cx: mir::Context<'db>,
    strand_entry: GBasicBlockId,
) -> bool {
    strand_entry.bb != strand_entry.func.data(db, mir_cx).entry_block
}

/// Returns the signature of the strand having the given entry point.
fn sig_for_strand<'db, 'bump>(
    db: &'db dyn Database,
    mir_cx: mir::Context<'db>,
    cx: &'bump LoweringCx,
    strand_entry: GBasicBlockId,
) -> Signature<'bump> {
    let mut param_types = bumpalo::collections::Vec::new_in(&cx.bump);

    // VM context
    param_types.push(ValTy::Int(IntBitness::B64));

    // If the strand is not a function entry, then
    // we pass an out pointer
    // for the returned continuation
    if does_strand_return_continuation(db, mir_cx, strand_entry) {
        param_types.push(ValTy::Int(IntBitness::B64));
    }

    // Basic block parameters
    let func_data = strand_entry.func.data(db, mir_cx);
    let bb_data = &func_data.basic_blocks[strand_entry.bb];
    let param_iter = bb_data
        .params
        .as_slice(&func_data.val_lists)
        .iter()
        .map(|&val| func_data.vals[val].typ);
    param_types.extend_from_slice(scalarize_types(db, mir_cx, param_iter, &cx.bump));

    let return_types = if does_strand_return_continuation(db, mir_cx, strand_entry) {
        // Returns the continuation tag
        cx.bump.alloc_slice_copy(&[ValTy::Int(IntBitness::B32)])
    } else {
        // Returns the function return value
        scalarize_type(db, mir_cx, func_data.header.return_type, &cx.bump)
    };

    Signature::new(param_types.into_bump_slice(), return_types)
}

struct Lowerer<'db, 'a, B> {
    db: &'db dyn Database,
    mir_cx: mir::Context<'db>,
    env: &'a dyn Env,
    isa: &'a Isa,
    backend: B,
    strand: &'a Strand,
    bump: &'a Bump,
    bb_map: HashMap<BbInstance<'a>, backend::BasicBlockId, &'a Bump>,
    val_map: HashMap<GValId, Compound<'a>, &'a Bump>,
    current_bb: BbInstance<'a>,
    current_func: &'a FuncData<'db>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct BbInstance<'bump> {
    bb: GBasicBlockId,
    call_stack: &'bump [FuncId],
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct GValId {
    func: mir::FuncId,
    val: mir::ValId,
}

impl<'db, 'a, B> Lowerer<'db, 'a, B>
where
    B: CodeBuilder<'a>,
{
    fn lower_bb(&mut self, instance: BbInstance<'a>, bb: &'db mir::BasicBlock<'db>) {
        self.backend.switch_to_block(self.bb_map[&instance]);
        self.current_bb = instance;
        self.current_func = instance.bb.func.resolve(self.db, self.mir_cx).data(self.db);

        for (_, instr) in &bb.instrs {
            self.lower_instr(instr);
        }

        todo!()
    }

    fn lower_instr(&mut self, instr: &mir::InstrData) {
        match instr {
            mir::InstrData::Jump(jump) => {
                todo!()
            }
            mir::InstrData::Branch(branch) => todo!(),
            mir::InstrData::Call(call) => todo!(),
            mir::InstrData::Return(_) => todo!(),
            mir::InstrData::Copy(unary) => todo!(),
            mir::InstrData::Constant(constant_instr) => todo!(),
            mir::InstrData::IntAdd(binary) => todo!(),
            mir::InstrData::IntSub(binary) => todo!(),
            mir::InstrData::IntMul(binary) => todo!(),
            mir::InstrData::IntDiv(binary) => todo!(),
            mir::InstrData::IntCmp(cmp) => todo!(),
            mir::InstrData::RealAdd(binary) => todo!(),
            mir::InstrData::RealSub(binary) => todo!(),
            mir::InstrData::RealMul(binary) => todo!(),
            mir::InstrData::RealDiv(binary) => todo!(),
            mir::InstrData::RealCmp(cmp) => todo!(),
            mir::InstrData::RealToInt(unary) => todo!(),
            mir::InstrData::IntToReal(unary) => todo!(),
            mir::InstrData::ByteToInt(unary) => todo!(),
            mir::InstrData::IntToByte(unary) => todo!(),
            mir::InstrData::BoolAnd(binary) => todo!(),
            mir::InstrData::BoolOr(binary) => todo!(),
            mir::InstrData::BoolXor(binary) => todo!(),
            mir::InstrData::BoolNot(unary) => todo!(),
            mir::InstrData::InitStruct(init_struct) => todo!(),
            mir::InstrData::GetField(get_field) => todo!(),
            mir::InstrData::SetField(set_field) => todo!(),
            mir::InstrData::Alloc(alloc) => todo!(),
            mir::InstrData::Load(load) => todo!(),
            mir::InstrData::Store(store) => todo!(),
            mir::InstrData::MakeFieldMRef(make_field_mref) => todo!(),
            mir::InstrData::MakeBufref(make_bufref) => todo!(),
            mir::InstrData::BufrefPush(bufref_push) => todo!(),
            mir::InstrData::BufrefRemove(bufref_remove) => todo!(),
            mir::InstrData::BufrefTrunc(bufref_trunc) => todo!(),
            mir::InstrData::BufrefLen(bufref_len) => todo!(),
            mir::InstrData::BufrefGet(bufref_get) => todo!(),
            mir::InstrData::BufregGetMRef(bufref_get_mref) => todo!(),
        }
    }

    /// Gets the Compound corresponding to the given
    /// mir in the current function.
    fn get_val(&self, val: mir::ValId) -> Compound<'a> {
        self.val_map[&GValId {
            val,
            func: self.current_bb.bb.func,
        }]
    }

    fn get_flattened_vals(
        &self,
        vals: impl IntoIterator<Item = mir::ValId>,
    ) -> &'a [backend::ValId] {
        let mut vec = bumpalo::collections::Vec::new_in(self.bump);

        for val in vals {
            vec.extend_from_slice_copy(self.get_val(val).flatten(self.bump));
        }

        vec.into_bump_slice()
    }

    fn bump_slice_append<T: Copy>(&self, slice: &[T], val: T) -> &'a [T] {
        let vec = bumpalo::collections::Vec::from_iter_in(
            slice.iter().copied().chain(iter::once(val)),
            self.bump,
        );
        vec.into_bump_slice()
    }
}
