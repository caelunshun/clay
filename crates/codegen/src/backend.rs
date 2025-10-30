/// Defines a backend that can produce machine code.
pub trait CodegenBackend {
    type CodeBuilder: CodeBuilder;
}

/// Builder for a MachFunc.
pub trait CodeBuilder {}
