pub mod whee {
    pub mod woo {}
}

use self::whee::woo as fo;

mod child {
    use crate::fo as bo;
}
