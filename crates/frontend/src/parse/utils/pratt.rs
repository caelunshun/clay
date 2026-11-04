#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Bp(pub u32);

impl Bp {
    pub const MIN: Self = Self(0);

    pub const fn new(base: u32, elevated: bool) -> Self {
        Self(base * 2 + elevated as u32)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct PrefixBp {
    pub right: Bp,
}

impl PrefixBp {
    pub const fn new(base: u32) -> Self {
        Self {
            right: Bp::new(base, false),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct PostfixBp {
    pub left: Bp,
}

impl PostfixBp {
    pub const fn new(base: u32) -> Self {
        Self {
            left: Bp::new(base, false),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct InfixBp {
    pub left: Bp,
    pub right: Bp,
}

impl InfixBp {
    pub const fn new_left(base: u32) -> Self {
        Self {
            left: Bp::new(base, false),
            right: Bp::new(base, true),
        }
    }

    pub const fn new_right(base: u32) -> Self {
        Self {
            left: Bp::new(base, true),
            right: Bp::new(base, false),
        }
    }
}
