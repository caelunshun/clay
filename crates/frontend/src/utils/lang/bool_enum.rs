#[doc(hidden)]
pub mod bool_enum_internals {
    pub use std::{
        clone::Clone,
        cmp::{Eq, Ord, PartialEq, PartialOrd},
        default::Default,
        fmt::Debug,
        hash::Hash,
        marker::Copy,
        primitive::bool,
    };
}

#[macro_export]
macro_rules! bool_enum {
    ($(
        $(#[$($attr:tt)*])*
        $vis:vis enum $name:ident {
            true => $truthy:ident;
            false => $falsy:ident;
        }
    )*) => {$(
        $(#[$($attr)*])*
        #[derive(
            $crate::utils::lang::bool_enum_internals::Debug,
            $crate::utils::lang::bool_enum_internals::Copy,
            $crate::utils::lang::bool_enum_internals::Clone,
            $crate::utils::lang::bool_enum_internals::Hash,
            $crate::utils::lang::bool_enum_internals::Eq,
            $crate::utils::lang::bool_enum_internals::PartialEq,
            $crate::utils::lang::bool_enum_internals::Ord,
            $crate::utils::lang::bool_enum_internals::PartialOrd,
            $crate::utils::lang::bool_enum_internals::Default,
        )]
        $vis enum $name {
            #[default]
            $falsy,
            $truthy,
        }

        #[allow(unused)]
        impl $name {
            pub const fn from_bool(v: $crate::utils::lang::bool_enum_internals::bool) -> Self {
                match v {
                    true => Self::$truthy,
                    false => Self::$falsy,
                }
            }

            pub const fn is_truthy(self) -> $crate::utils::lang::bool_enum_internals::bool {
                match self {
                    Self::$truthy => true,
                    Self::$falsy => false,
                }
            }

            pub const fn is_falsy(self) -> $crate::utils::lang::bool_enum_internals::bool {
                match self {
                    Self::$truthy => false,
                    Self::$falsy => true,
                }
            }

            pub const fn flip(self) -> Self {
                match self {
                    Self::$truthy => Self::$falsy,
                    Self::$falsy => Self::$truthy,
                }
            }
        }
    )*};
}

pub use bool_enum;
