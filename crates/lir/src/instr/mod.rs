use crate::instr::integer::IntAdd;
use clay_core::ghost_heap::GhostPtr;

pub mod bool_;
pub mod call;
pub mod control_flow;
pub mod enum_;
pub mod float;
pub mod integer;
pub mod reference;
pub mod strukt;

#[macro_export]
macro_rules! instr {
    (pub struct $ident:ident {
        $(pub $field:ident : $field_ty:ty),* $(,)?
    }) => {
        pub struct $ident<'g> {
            pub base: $crate::instr::InstrBase<'g>,
            $(
                pub $field : $field_ty,
            )*
        }

        unsafe impl <'g> ::clay_core::ghost_heap::GhostPointee<'g> for $ident<'g> {
            type ForLt<'new_g> = $ident<'new_g>;
        }

        impl <'g> $ident<'g> {
            pub fn next(&self) -> Option<$crate::instr::InstrPtr<'g>> {
                self.base.next
            }

            pub fn prev(&self) -> Option<$crate::instr::InstrPtr<'g>> {
                self.base.prev
            }
        }
    };
}

pub struct InstrBase<'g> {
    pub next: Option<InstrPtr<'g>>,
    pub prev: Option<InstrPtr<'g>>,
}

macro_rules! instr_ptr_enum {
    ($($variant:ident),* $(,)?) => {
        #[derive(Copy, Clone)]
        pub enum InstrPtr<'g> {
            $(
                $variant(GhostPtr<'g, $variant<'g>>)
            )*
        }
    }
}

instr_ptr_enum!(IntAdd);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CmpMode {
    Less,
    LessOrEqual,
    Equal,
    NotEqual,
    Greater,
    GreaterOrEqual,
}
