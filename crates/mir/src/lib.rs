#![feature(if_let_guard)]

#[macro_export]
macro_rules! entity_ref {
    {
        $(#[$attr:meta])*
        pub struct $ident:ident;
    } => {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default, PartialOrd, Ord, bytemuck::Pod, bytemuck::Zeroable, salsa::Update)]
        #[repr(transparent)]
        $(#[$attr])*
        pub struct $ident(u32);

        impl ::cranelift_entity::EntityRef for $ident {
            fn new(i: usize) -> Self {
                if i >= u32::MAX as usize {
                    // u32::MAX is a reserved value
                    panic!(concat!("too many entities refs of type ", stringify!($ident)));
                }
                Self(i as u32)
            }

            fn index(self) -> usize {
                self.0 as usize
            }
        }

        impl ::cranelift_entity::packed_option::ReservedValue for $ident {
            fn is_reserved_value(&self) -> bool {
                self.0 == u32::MAX
            }

            fn reserved_value() -> Self {
                Self(u32::MAX)
            }
        }
    };
}

#[macro_export]
macro_rules! entity_ref_16bit {
     {
         $(#[$attr:meta])*
        pub struct $ident:ident;
    } => {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default, PartialOrd, Ord, bytemuck::Pod, bytemuck::Zeroable, salsa::Update)]
        #[repr(transparent)]
            $(#[$attr])*
        pub struct $ident(u16);

        impl ::cranelift_entity::EntityRef for $ident {
            fn new(i: usize) -> Self {
                if i >= u16::MAX as usize {
                    // u16::MAX is a reserved value
                     panic!(concat!("too many entities refs of type ", stringify!($ident)));
                }
                Self(i as u16)
            }

            fn index(self) -> usize {
                self.0 as usize
            }
        }

        impl ::cranelift_entity::packed_option::ReservedValue for $ident {
            fn is_reserved_value(&self) -> bool {
                self.0 == u16::MAX
            }

            fn reserved_value() -> Self {
                Self(u16::MAX)
            }
        }
    };
}

pub mod builder;
// pub mod formatter;
pub mod ir;
//pub mod parser;
pub mod passes;
pub mod trait_resolution;
pub mod validation;

pub use ir::{Func, PrimType, TypeKind, ValId, instr::InstrData};
