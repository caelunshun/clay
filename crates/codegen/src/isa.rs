/// An ISA supported by fir.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Isa {
    /// X64.
    X86_64(ExtensionsX86_64),
    /// ARM64.
    Aarch64(ExtensionsAarch64),
    /// RISC-V, 64-bit variant with 32 registers.
    /// M, F, D, and A extensions are required.
    Rv64i(ExtensionsRv64i),
}

impl Isa {
    /// Gets the ISA of the current system.
    ///
    /// Panics if this system is not supported by fir.
    #[allow(unreachable_code)]
    #[allow(clippy::assertions_on_constants)]
    pub fn native() -> Self {
        #[cfg(target_arch = "x86_64")]
        {
            use std::arch::is_x86_feature_detected;
            assert!(
                is_x86_feature_detected!("sse2"),
                "on x64, SSE2 support is required"
            );
            assert!(
                is_x86_feature_detected!("cmpxchg16b"),
                "on x64, cmpxchg16b support is required"
            );

            return Self::X86_64(ExtensionsX86_64 {
                avx: is_x86_feature_detected!("avx"),
                avx2: is_x86_feature_detected!("avx2"),
            });
        }

        #[cfg(target_arch = "aarch64")]
        {
            return Self::Aarch64(ExtensionsAarch64 {});
        }

        #[cfg(target_arch = "riscv64")]
        {
            use std::arch::is_riscv_feature_detected;
            assert!(
                is_riscv_feature_detected!("a"),
                "on rv64i, A extension is required"
            );
            assert!(
                is_riscv_feature_detected!("m"),
                "on rv64i, M extension is required"
            );
            assert!(
                is_riscv_feature_detected!("f"),
                "on rv64i, F extension is required"
            );
            assert!(
                is_riscv_feature_detected!("d"),
                "on rv64i, D extension is required"
            );
        }

        panic!("this ISA is not supported by fir")
    }

    pub fn pointer_width(&self) -> PointerWidth {
        match self {
            Isa::X86_64(_) | Isa::Aarch64(_) | Isa::Rv64i(_) => PointerWidth::P64,
        }
    }

    pub fn supports_64bit_atomics(&self) -> bool {
        true
    }

    pub fn supports_128bit_atomics(&self) -> bool {
        match self {
            Isa::X86_64(_) | Isa::Aarch64(_) => true,
            Isa::Rv64i(_) => false,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PointerWidth {
    P32,
    P64,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExtensionsX86_64 {
    pub avx: bool,
    pub avx2: bool,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExtensionsAarch64 {}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExtensionsRv64i {}
