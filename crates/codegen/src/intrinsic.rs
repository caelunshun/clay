use crate::backend::{IntBitness, Signature, ValTy};

/// A function provided by the runtime.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum IntrinsicCall {
    /// Allocate GC-managed memory.
    GcAlloc,
    /// Slow-path implementation of bufref.push
    /// for cases where the bufref doesn't point
    /// to the start of the buffer, or where there
    /// is insufficient capacity in the buffer to push an item.
    BufrefPushSlow,
    /// Safepoint that should be invoked if request_pause
    /// in the VM context is true.
    Safepoint,
    /// On-stack replacement implementation, used
    /// to upgrade the optimization of a function
    /// while it is running.
    OnStackReplace,
}

impl IntrinsicCall {
    pub fn signature(self) -> Signature<'static> {
        match self {
            IntrinsicCall::GcAlloc => {
                // Parameters:
                // (1) size
                // (2) alignment
                // Returns:
                // (1) the allocated pointer.
                static PARAMS: &[ValTy] =
                    &[ValTy::Int(IntBitness::B64), ValTy::Int(IntBitness::B64)];
                static RETURNS: &[ValTy] = &[ValTy::Int(IntBitness::B64)];
                Signature::new(PARAMS, RETURNS)
            }
            IntrinsicCall::BufrefPushSlow => {
                // Parameters:
                // (1) bufref address
                // (2) bufref len
                // (3) reference to the value to push
                // Returns:
                // (1) new bufref address
                // (2) new bufref len
                static PARAMS: &[ValTy] = &[
                    ValTy::Int(IntBitness::B64),
                    ValTy::Int(IntBitness::B64),
                    ValTy::Int(IntBitness::B64),
                ];
                static RETURNS: &[ValTy] =
                    &[ValTy::Int(IntBitness::B64), ValTy::Int(IntBitness::B64)];
                Signature::new(PARAMS, RETURNS)
            }
            IntrinsicCall::Safepoint => {
                // Parameters: none.
                // Returns: none.
                Signature::new(&[], &[])
            }
            IntrinsicCall::OnStackReplace => {
                // Parameters: none.
                // Returns: none.
                Signature::new(&[], &[])
            }
        }
    }
}
