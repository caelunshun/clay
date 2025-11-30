//! Lowering of MIR strands to the codegen backend.

use crate::{
    backend::{
        self, BasicBlockId, CodeBuilder, CodegenBackend, FloatBitness, IntBitness, Signature, ValTy,
    },
    compiled_strand::{CompiledStrand, Symbol},
    isa::Isa,
    lowering::{
        compound_val::{Compound, scalarize_type, scalarize_types},
        context::LoweringCx,
        env::Env,
    },
    strand::{self, CallStackEntry, GBasicBlockId, Strand},
};
use bumpalo::Bump;
use cranelift_entity::SecondaryMap;
use fir_core::{HashMap, HashSet};
use mir::{FuncData, TypeArgs};
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
) -> CompiledStrand<'db>
where
    B: CodegenBackend,
{
    thread_local! {
        static LOWERING_CX: LazyCell<RefCell<LoweringCx>> = LazyCell::new(Default::default);
    }

    LOWERING_CX.with(|cx_cell| {
        let mut cx = cx_cell.borrow_mut();

        let entry_block = strand.entry().resolve(db, mir_cx);
        let entry_block_func = strand.entry_func().id(db).data(db, mir_cx);

        let sig = sig_for_strand(db, mir_cx, &cx.bump, strand.entry());

        {
            let mut lowerer = Lowerer {
                db,
                mir_cx,
                env,
                isa: backend.isa(),
                backend: backend.make_code_builder(db, &cx.bump, sig),
                strand,
                bump: &cx.bump,
                bb_map: HashMap::new_in(&cx.bump),
                current_vals: SecondaryMap::default(),
                current_mir_bb: BbInstance {
                    bb: strand.entry(),
                    call_site: &[],
                },
                current_backend_bb: Default::default(),
                current_func: entry_block_func,
                current_type_args: strand.entry_type_args().clone(),
                initialize_aux_blocks: Vec::new(),
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
    strand_entry.bb != strand_entry.func.id(db).data(db, mir_cx).entry_block
}

/// Returns the signature of the strand having the given entry point.
fn sig_for_strand<'db, 'bump>(
    db: &'db dyn Database,
    mir_cx: mir::Context<'db>,
    bump: &'bump Bump,
    strand_entry: GBasicBlockId,
) -> Signature<'bump> {
    let mut param_types = bumpalo::collections::Vec::new_in(bump);

    // VM context
    param_types.push(ValTy::Int(IntBitness::B64));

    // If the strand is not a function entry, then
    // we pass an out pointer
    // for the returned continuation
    if does_strand_return_continuation(db, mir_cx, strand_entry) {
        param_types.push(ValTy::Int(IntBitness::B64));
    }

    // Basic block parameters
    let func_data = strand_entry.func.id(db).data(db, mir_cx);
    let bb_data = &func_data.basic_blocks[strand_entry.bb];
    let param_iter = bb_data
        .params
        .as_slice(&func_data.val_lists)
        .iter()
        .map(|&val| func_data.vals[val].typ);
    param_types.extend_from_slice(scalarize_types(db, mir_cx, param_iter, bump));

    let return_types = if does_strand_return_continuation(db, mir_cx, strand_entry) {
        // Returns the continuation tag
        bump.alloc_slice_copy(&[ValTy::Int(IntBitness::B32)])
    } else {
        // Returns the function return value
        scalarize_type(db, mir_cx, func_data.header.return_type, bump)
    };

    Signature::new(param_types.into_bump_slice(), return_types)
}

struct Lowerer<'db, 'tmp, B> {
    db: &'db dyn Database,
    mir_cx: mir::Context<'db>,
    env: &'tmp dyn Env,
    isa: &'tmp Isa,
    backend: B,
    strand: &'tmp Strand<'db>,
    bump: &'tmp Bump,
    /// Maps mir basic blocks to the corresponding blocks in the backend.
    /// Note that in some cases, a mir block can generate multiple backend
    /// basic blocks, e.g. for certain high-level instructions that produce
    /// branches. In these cases, the bb_map entry points to the "entry"/"initial"
    /// block of the mir basic block, which is always unique.
    bb_map: HashMap<BbInstance<'db, 'tmp>, backend::BasicBlockId, &'tmp Bump>,
    current_mir_bb: BbInstance<'db, 'tmp>,
    current_backend_bb: BasicBlockId,
    current_func: &'tmp FuncData<'db>,
    current_vals: SecondaryMap<mir::ValId, Option<Compound<'tmp>>>,
    /// Type arguments in the current function.
    current_type_args: TypeArgs<'db>,

    /// Collection of callbacks to initialize extra basic blocks at the end.
    initialize_aux_blocks: Vec<Box<dyn FnOnce(&mut Self)>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct BbInstance<'db, 'tmp> {
    bb: GBasicBlockId<'db>,
    call_site: &'tmp [CallStackEntry],
}

impl<'db, 'tmp, B> Lowerer<'db, 'tmp, B>
where
    B: CodeBuilder<'db, 'tmp>,
    'db: 'tmp,
{
    /// Performs an initial traversal of the BbInstances to compile,
    /// populating bb_map with their mapping to backend BasicBlocks.
    pub fn populate_bbs(&mut self) {
        let mut stack = bumpalo::collections::Vec::new_in(self.bump);
        stack.push(BbInstance::<'db, 'tmp> {
            bb: self.strand.entry(),
            call_site: &[],
        });

        let mut visited = HashSet::new_in(self.bump);
        visited.insert(stack[0]);

        while let Option::<BbInstance<'db, 'tmp>>::Some(current) = stack.pop() {
            let backend_bb = self.backend.create_block();
            self.bb_map.insert(current, backend_bb);

            // Populate parameter types
            let func_data = current.bb.func.id(self.db).data(self.db, self.mir_cx);
            let param_types = func_data.basic_blocks[current.bb.bb]
                .params
                .as_slice(&func_data.val_lists)
                .iter()
                .map(|&val| func_data.vals[val].typ);
            let param_types = scalarize_types(self.db, self.mir_cx, param_types, self.bump);
            for &param_ty in param_types {
                self.backend.append_block_param(backend_bb, param_ty);
            }

            // Traverse successors within this strand
            let mut successors = bumpalo::collections::Vec::new_in(self.bump);
            func_data.visit_block_successors(current.bb.bb, |successor| {
                successors.push((
                    GBasicBlockId {
                        func: current.bb.func,
                        bb: successor,
                    },
                    func_data.basic_blocks[current.bb.bb]
                        .instrs
                        .last()
                        .unwrap()
                        .0,
                ));
            });
            func_data.visit_block_called_funcs(current.bb.bb, |instr, abstract_func| {
                let func = abstract_func
                    .resolve(self.db, self.mir_cx, &self.current_type_args)
                    .expect("assoc func unresolved?");
                successors.push((
                    GBasicBlockId {
                        func,
                        bb: func.id(self.db).data(self.db, self.mir_cx).entry_block,
                    },
                    instr,
                ));
            });

            for (successor, instr) in successors {
                let call_site = if successor.func == current.bb.func {
                    current.call_site
                } else {
                    self.bump_slice_append(
                        current.call_site,
                        CallStackEntry {
                            func: current.bb.func.id(self.db),
                            jump_bb: current.bb.bb,
                            jump_instr: instr,
                        },
                    )
                };

                let target = strand::Exit {
                    call_site: call_site.to_vec(),
                    target: successor,
                };
                if !self.strand.is_exit(target) {
                    let bb_instance = BbInstance {
                        bb: successor,
                        call_site,
                    };
                    if visited.insert(bb_instance) {
                        stack.push(bb_instance);
                    }
                }
            }
        }
    }

    fn lower_bb(&mut self, instance: BbInstance<'db, 'tmp>, bb: &'db mir::BasicBlock<'db>) {
        self.backend.switch_to_block(self.bb_map[&instance]);
        self.current_backend_bb = self.bb_map[&instance];
        self.current_mir_bb = instance;
        self.current_func = instance
            .bb
            .func
            .id(self.db)
            .resolve(self.db, self.mir_cx)
            .data(self.db);

        self.current_vals.clear();

        let mut bb_params = self.backend.block_params().iter().copied();

        for param in self.current_func.basic_blocks[self.current_mir_bb.bb.bb]
            .params
            .as_slice(&self.current_func.val_lists)
        {
            let param_val = Compound::from_flat(
                self.db,
                self.mir_cx,
                self.bump,
                &mut bb_params,
                self.current_func.vals[*param].typ,
            );
            self.current_vals[*param] = Some(param_val);
        }

        for (_, instr) in &bb.instrs {
            self.lower_instr(instr);
        }
    }

    fn lower_instr(&mut self, instr: &mir::InstrData) {
        match instr {
            mir::InstrData::Jump(jump) => {
                let target = self.get_jump_target(jump.target);
                let args = self.get_flattened_vals(
                    jump.args
                        .as_slice(&self.current_func.val_lists)
                        .iter()
                        .copied(),
                );
                self.backend.jump(target, args);
            }
            mir::InstrData::Branch(branch) => {
                let target_true = self.get_jump_target(branch.target_true);
                let args_true = self.get_flattened_vals(
                    branch
                        .args_true
                        .as_slice(&self.current_func.val_lists)
                        .iter()
                        .copied(),
                );

                let target_false = self.get_jump_target(branch.target_false);
                let args_false = self.get_flattened_vals(
                    branch
                        .args_false
                        .as_slice(&self.current_func.val_lists)
                        .iter()
                        .copied(),
                );

                let Compound::Bool(condition) = self.get_val(branch.condition) else {
                    panic!("expected condition to be a bool");
                };

                self.backend
                    .branch(condition, target_true, args_true, target_false, args_false);
            }
            mir::InstrData::Call(call) => {
                // TODO strand inline logic
                // For now, always assume not inlined
                let target_func = call
                    .func
                    .resolve(self.db, self.mir_cx, &self.current_type_args)
                    .expect("unresolved assoc func");
                let strand_entry = GBasicBlockId {
                    func: target_func,
                    bb: target_func
                        .id(self.db)
                        .data(self.db, self.mir_cx)
                        .entry_block,
                };
                let sig = sig_for_strand(self.db, self.mir_cx, self.bump, strand_entry);
                let args = self.get_flattened_vals(
                    call.args
                        .as_slice(&self.current_func.val_lists)
                        .iter()
                        .copied(),
                );
                self.backend.call(
                    Symbol::StrandForBlock {
                        block: strand_entry,
                    },
                    sig,
                    args,
                );
            }
            mir::InstrData::Return(ret) => {
                // TODO non-root strand logic
                // For now, assume strand is the function root
                let vals = self.get_flattened_vals([ret.return_value]);
                self.backend.return_(vals);
            }
            mir::InstrData::Copy(unary) => {
                self.current_vals[unary.dst] = self.current_vals[unary.src];
            }
            mir::InstrData::Constant(constant_instr) => {
                let val = match constant_instr.constant.value(self.db) {
                    mir::ConstantValue::Int(x) => {
                        Compound::Int(self.backend.int_const(*x, IntBitness::B64))
                    }
                    mir::ConstantValue::Real(x) => {
                        Compound::Real(self.backend.float_const(*x, FloatBitness::B64))
                    }
                    mir::ConstantValue::Bool(x) => {
                        Compound::Bool(self.backend.int_const(*x as i64, IntBitness::B8))
                    }
                    mir::ConstantValue::Str(_x) => {
                        todo!()
                    }
                };
                self.current_vals[constant_instr.dst] = Some(val);
            }
            mir::InstrData::IntAdd(binary) => {
                let Compound::Int(lhs) = self.get_val(binary.src1) else {
                    panic!("not an int")
                };
                let Compound::Int(rhs) = self.get_val(binary.src2) else {
                    panic!("not an int")
                };
                let dst = Compound::Int(self.backend.int_add(lhs, rhs));
                self.current_vals[binary.dst] = Some(dst);
            }
            mir::InstrData::IntSub(binary) => {
                let Compound::Int(lhs) = self.get_val(binary.src1) else {
                    panic!("not an int")
                };
                let Compound::Int(rhs) = self.get_val(binary.src2) else {
                    panic!("not an int")
                };
                let dst = Compound::Int(self.backend.int_sub(lhs, rhs));
                self.current_vals[binary.dst] = Some(dst);
            }
            mir::InstrData::IntMul(binary) => {
                let Compound::Int(lhs) = self.get_val(binary.src1) else {
                    panic!("not an int")
                };
                let Compound::Int(rhs) = self.get_val(binary.src2) else {
                    panic!("not an int")
                };
                let dst = Compound::Int(self.backend.int_mul(lhs, rhs));
                self.current_vals[binary.dst] = Some(dst);
            }
            mir::InstrData::IntDiv(binary) => {
                let Compound::Int(lhs) = self.get_val(binary.src1) else {
                    panic!("not an int")
                };
                let Compound::Int(rhs) = self.get_val(binary.src2) else {
                    panic!("not an int")
                };
                let dst = Compound::Int(self.backend.int_sdiv(lhs, rhs));
                self.current_vals[binary.dst] = Some(dst);
            }
            mir::InstrData::IntCmp(cmp) => {}
            mir::InstrData::RealAdd(binary) => {
                let Compound::Real(lhs) = self.get_val(binary.src1) else {
                    panic!("not a real")
                };
                let Compound::Real(rhs) = self.get_val(binary.src2) else {
                    panic!("not a real")
                };
                let dst = Compound::Real(self.backend.float_add(lhs, rhs));
                self.current_vals[binary.dst] = Some(dst);
            }
            mir::InstrData::RealSub(binary) => {
                let Compound::Real(lhs) = self.get_val(binary.src1) else {
                    panic!("not a real")
                };
                let Compound::Real(rhs) = self.get_val(binary.src2) else {
                    panic!("not a real")
                };
                let dst = Compound::Real(self.backend.float_sub(lhs, rhs));
                self.current_vals[binary.dst] = Some(dst);
            }
            mir::InstrData::RealMul(binary) => {
                let Compound::Real(lhs) = self.get_val(binary.src1) else {
                    panic!("not a real")
                };
                let Compound::Real(rhs) = self.get_val(binary.src2) else {
                    panic!("not a real")
                };
                let dst = Compound::Real(self.backend.float_mul(lhs, rhs));
                self.current_vals[binary.dst] = Some(dst);
            }
            mir::InstrData::RealDiv(binary) => {
                let Compound::Real(lhs) = self.get_val(binary.src1) else {
                    panic!("not a real")
                };
                let Compound::Real(rhs) = self.get_val(binary.src2) else {
                    panic!("not a real")
                };
                let dst = Compound::Real(self.backend.float_div(lhs, rhs));
                self.current_vals[binary.dst] = Some(dst);
            }
            mir::InstrData::RealCmp(cmp) => todo!(),
            mir::InstrData::RealToInt(unary) => {
                let Compound::Real(src) = self.get_val(unary.src) else {
                    panic!("not a real")
                };
                let dst = Compound::Int(self.backend.float_sat_trunc_to_int(src, IntBitness::B64));
                self.current_vals[unary.dst] = Some(dst);
            }
            mir::InstrData::IntToReal(unary) => {
                let Compound::Int(src) = self.get_val(unary.src) else {
                    panic!("not an int")
                };
                let dst = Compound::Real(self.backend.int_to_nearest_float(src, FloatBitness::B64));
                self.current_vals[unary.dst] = Some(dst);
            }
            mir::InstrData::ByteToInt(unary) => {
                let Compound::Byte(src) = self.get_val(unary.src) else {
                    panic!("not a byte")
                };
                let dst = Compound::Int(self.backend.int_zext(src, IntBitness::B64));
                self.current_vals[unary.dst] = Some(dst);
            }
            mir::InstrData::IntToByte(unary) => {
                let Compound::Int(src) = self.get_val(unary.src) else {
                    panic!("not an int")
                };
                let dst = Compound::Byte(self.backend.int_trunc(src, IntBitness::B8));
                self.current_vals[unary.dst] = Some(dst);
            }
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

    /// Gets the basic block that should be jumped to for a particular
    /// jump target.
    /// * If the target block is inside the current strand and current function, then
    /// we just return that block.
    /// * If the target block is outside the current strand, but in the current function,
    /// then we generate a new block that calls the sub-strand and return that block.
    fn get_jump_target(&mut self, mir_target: mir::BasicBlockId) -> BasicBlockId {
        let query_instance = BbInstance {
            bb: GBasicBlockId {
                func: self.current_mir_bb.bb.func,
                bb: mir_target,
            },
            call_site: self.current_mir_bb.call_site,
        };

        if let Some(mapped_bb) = self.bb_map.get(&query_instance) {
            return *mapped_bb;
        }

        // Not in current strand/function; generate a new block that produces a call.

        todo!()
    }

    /// Gets the Compound corresponding to the given
    /// mir in the current function.
    fn get_val(&self, val: mir::ValId) -> Compound<'tmp> {
        self.current_vals[val].expect("value not in current_vals? maybe not SSA?")
    }

    fn get_flattened_vals(
        &self,
        vals: impl IntoIterator<Item = mir::ValId>,
    ) -> &'tmp [backend::ValId] {
        let mut vec = bumpalo::collections::Vec::new_in(self.bump);

        for val in vals {
            vec.extend_from_slice_copy(self.get_val(val).flatten(self.bump));
        }

        vec.into_bump_slice()
    }

    fn bump_slice_append<T: Copy>(&self, slice: &[T], val: T) -> &'tmp [T] {
        let vec = bumpalo::collections::Vec::from_iter_in(
            slice.iter().copied().chain(iter::once(val)),
            self.bump,
        );
        vec.into_bump_slice()
    }
}
