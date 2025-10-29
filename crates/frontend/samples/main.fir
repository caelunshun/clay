use {{{{{{{{{self}}}}}}}}};

pub mod meow {
    pub use super::thump::*;

    pub mod whee {}
}

pub mod thump {
    pub use super::meow::*;

    pub mod whee {}
}

pub use meow::whee as first;
pub use thump::whee as second;

pub mod res {
    pub use {crate::meow::*, crate::thump::*};
}

use res::{whee as third};
