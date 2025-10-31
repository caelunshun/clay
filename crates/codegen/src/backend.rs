use crate::compiled_strand::CompiledStrand;
use bumpalo::Bump;
use fir_mir::{
    entity_ref,
    instr::{CompareMode, LoadOrdering, StoreOrdering},
};
use std::hash::Hash;

/// Defines a backend that can produce machine code.
pub trait CodegenBackend {
    type CodeBuilder<'bump>: CodeBuilder<'bump>;

    /// Creates a new builder for a machine-level function.
    ///
    /// It will be initialized with an entry block having arguments matching
    /// the provided signature.
    fn make_code_builder<'bump>(
        &self,
        bump: &'bump Bump,
        signature: Signature<'bump>,
    ) -> Self::CodeBuilder<'bump>;
}

/// Builder for a CompiledStrand (machine-level function).
pub trait CodeBuilder<'bump> {
    type Backend: CodegenBackend;

    /// Finishes compilation of this function.
    fn finish(self) -> CompiledStrand;

    /// Gets the ID of the current block.
    /// This is the entry block initially.
    fn current_block(&self) -> BasicBlockId;

    /// Gets the value at the given index for a parameter of the current block.
    fn block_param(&self, index: u32) -> ValId;

    /// Creates a new basic block.
    fn create_block(&mut self) -> BasicBlockId;

    /// Appends an argument to a basic block.
    fn append_block_param(&mut self, block: BasicBlockId, ty: ValTy);

    /// Switches to the given basic block.
    ///
    /// A block can only be switched to once.
    /// It is illegal to switch back to a block
    /// that has already been written to.
    fn switch_to_block(&mut self, block: BasicBlockId);

    // ---- INSTRUCTIONS ----
    /// Creates a constant integer value.
    fn int_const(&mut self, imm: i64, bitness: IntBitness) -> ValId;

    // Integer arithmetic.
    // Bit width of both arguments must match,
    // and the bit width of the output will equal
    // the bit width of the inputs.

    fn int_add(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn int_sub(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn int_mul(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn int_sdiv(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn int_udiv(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn int_srem(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn int_urem(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn int_and(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn int_or(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn int_xor(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn int_not(&mut self, arg: ValId) -> ValId;

    fn int_sll(&mut self, arg: ValId, shamt: ValId) -> ValId;
    fn int_srl(&mut self, arg: ValId, shamt: ValId) -> ValId;
    fn int_sra(&mut self, arg: ValId, shamt: ValId) -> ValId;

    fn int_trunc(&mut self, arg: ValId, dst_bitness: IntBitness) -> ValId;
    fn int_zext(&mut self, arg: ValId, dst_bitness: IntBitness) -> ValId;
    fn int_sext(&mut self, arg: ValId, dst_bitness: IntBitness) -> ValId;

    // Comparison instructions. Output is int8 boolean (0 or 1).
    fn int_scmp(&mut self, lhs: ValId, rhs: ValId, mode: CompareMode) -> ValId;
    fn int_ucmp(&mut self, lhs: ValId, rhs: ValId, mode: CompareMode) -> ValId;

    fn int_to_nearest_float(&mut self, arg: ValId, dst_bitness: FloatBitness) -> ValId;
    fn int_bitcast_to_float(&mut self, arg: ValId) -> ValId;

    /// Creates a constant float value.
    fn float_const(&mut self, imm: f64, bitness: FloatBitness) -> ValId;

    // Floating-point arithmetic.
    // Round to nearest, ties even.
    // NaN handling is arbitrary.
    // Bit width of both arguments must match,
    // and the bit width of the output will equal
    // the bit width of the inputs.

    fn float_add(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn float_sub(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn float_mul(&mut self, lhs: ValId, rhs: ValId) -> ValId;
    fn float_div(&mut self, lhs: ValId, rhs: ValId) -> ValId;

    fn float_cmp(&mut self, lhs: ValId, rhs: ValId, mode: CompareMode) -> ValId;

    fn float_sat_trunc_to_int(&mut self, arg: ValId, dst_bitness: IntBitness) -> ValId;
    fn float_bitcast_to_int(&mut self, arg: ValId) -> ValId;

    // Memory instructions.
    //
    // Alignment requirements: All loads and stores must be naturally aligned,
    // or the behavior is undefined.
    //
    // Obviously, load and store addresses need to point to valid memory
    // or the behavior is undefined.

    fn mem_load(
        &mut self,
        addr: ValId,
        imm_offset: i32,
        ty: ValTy,
        ordering: LoadOrdering,
    ) -> ValId;
    fn mem_store(&mut self, val: ValId, addr: ValId, imm_offset: i32, ordering: StoreOrdering);
    /// Atomic compare-exchange.
    ///
    /// Returns a boolean indicating whether the exchange succeeded,
    /// as well as the previous value.
    fn mem_compare_exchange(
        &mut self,
        val: ValId,
        addr: ValId,
        imm_offset: i32,
        load_ordering: LoadOrdering,
        store_ordering: StoreOrdering,
    ) -> CompareExchangeResult;

    // Special 128-bit atomics.
    // We don't have an int128 type,
    // but we do need 128-bit atomics
    // to soundly implement certain runtime
    // features (e.g. fat pointers).
    // These instructions operate on double-values,
    // where the first corresponds to the low 64 bits and the
    // second the high 64 bits.
    fn mem_load128(&mut self, addr: ValId, imm_offset: i32, ordering: LoadOrdering) -> [ValId; 2];
    fn mem_store128(
        &mut self,
        val: [ValId; 2],
        addr: ValId,
        imm_offset: i32,
        ordering: StoreOrdering,
    );
    fn mem_compare_exchange128(
        &mut self,
        val: [ValId; 2],
        addr: ValId,
        imm_offset: i32,
        load_ordering: LoadOrdering,
        store_ordering: StoreOrdering,
    ) -> CompareExchangeResult128;

    /// Instruction that tells the processor we are in a spin-wait loop.
    /// Implementation as a no-op is valid.
    fn hint_spin_loop(&mut self);

    /// Call a function whose address is given as a pointer-sized
    /// integer in `addr`, and whose signature must match the given signature.
    /// Assumes SystemV calling convention. Return values are returned
    /// in a slice.
    fn call_indirect(&mut self, addr: ValId, sig: Signature, args: &[ValId]) -> &'bump [ValId];

    // Block terminators.

    fn jump(&mut self, block: BasicBlockId, args: &[ValId]);
    /// Condition should be int8 (boolean). Unspecified behavior
    /// if condition is not 0 or 1.
    fn branch(
        &mut self,
        condition: ValId,
        true_block: BasicBlockId,
        true_args: &[ValId],
        false_block: BasicBlockId,
        false_args: &[ValId],
    );
    fn return_(&mut self, return_vals: &[ValId]);
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct CompareExchangeResult {
    pub success: ValId,
    pub previous_val: ValId,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct CompareExchangeResult128 {
    pub success: ValId,
    pub previous_val: [ValId; 2],
}

entity_ref! {
    /// ID of a low-level scalar value.
    ///
    /// Distinc from mir::ValId, which is an aggregate value.
    pub struct ValId;
}

entity_ref! {
    /// ID of a low-level basic block.
    ///
    /// Not necessarily one-to-one with MIR basic blocks,
    /// since some MIR instructions, when lowered, may introduce
    /// extra conditionals and thus basic blocks.
    pub struct BasicBlockId;
}

/// Type of a value in the low-level IR.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ValTy {
    Int(IntBitness),
    Float(FloatBitness),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum IntBitness {
    B8,
    B32,
    B64,
}

impl IntBitness {
    pub fn to_float(self) -> Option<FloatBitness> {
        match self {
            IntBitness::B64 => Some(FloatBitness::B64),
            _ => None,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum FloatBitness {
    B64,
}

impl FloatBitness {
    pub fn to_int(self) -> IntBitness {
        match self {
            FloatBitness::B64 => IntBitness::B64,
        }
    }
}

/// Signature of a machine-level function.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Signature<'bump> {
    pub param_types: &'bump [ValTy],
    pub return_types: &'bump [ValTy],
}

impl<'bump> Signature<'bump> {
    pub fn new(param_types: &'bump [ValTy], return_types: &'bump [ValTy]) -> Self {
        Self {
            param_types,
            return_types,
        }
    }
}
