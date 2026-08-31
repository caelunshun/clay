use derive_where::derive_where;
use std::{num::NonZeroU32, ops::Range};

const OVERFLOW_ERR: &str = "overflowed debruijn index";

const fn usize_to_u32(v: usize) -> Option<u32> {
    if v as u32 as usize == v {
        Some(v as u32)
    } else {
        None
    }
}

#[derive(Debug, Clone)]
pub struct DebruijnTop {
    head: DebruijnAbsolute,
}

impl Default for DebruijnTop {
    fn default() -> Self {
        Self::ZERO
    }
}

impl DebruijnTop {
    pub const ZERO: Self = Self::new(0);

    #[must_use]
    pub const fn new(v: usize) -> Self {
        Self {
            head: DebruijnAbsolute::new(v),
        }
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.head.index()
    }

    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub const fn move_inwards(&mut self) -> DebruijnAbsolute {
        self.move_inwards_by(1).start()
    }

    pub const fn move_outwards(&mut self) -> DebruijnAbsolute {
        self.move_outwards_by(1).start()
    }

    pub const fn move_inwards_by(&mut self, by: usize) -> DebruijnAbsoluteRange {
        let old_head = DebruijnAbsoluteRange::new(self.head, by);
        self.head = self.head.inward(by);
        old_head
    }

    pub const fn move_outwards_by(&mut self, by: usize) -> DebruijnAbsoluteRange {
        let old_head = DebruijnAbsoluteRange::new(self.head, by);
        self.head = self.head.outward(by);
        old_head
    }

    #[must_use]
    pub const fn make_relative(&self, index: DebruijnAbsolute) -> DebruijnRelative {
        self.head.delta_to_outer(index)
    }

    #[must_use]
    pub const fn try_lookup_relative(&self, index: DebruijnRelative) -> Option<DebruijnAbsolute> {
        self.head.try_lookup_outer(index)
    }

    #[must_use]
    pub const fn lookup_relative(&self, index: DebruijnRelative) -> DebruijnAbsolute {
        self.head.lookup_outer(index)
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct DebruijnAbsoluteRange {
    start: DebruijnAbsolute,
    len: u32,
}

impl DebruijnAbsoluteRange {
    #[must_use]
    pub const fn new(start: DebruijnAbsolute, len: usize) -> Self {
        Self {
            start,
            len: usize_to_u32(len).expect("length too large"),
        }
    }

    #[must_use]
    pub const fn start(self) -> DebruijnAbsolute {
        self.start
    }

    #[must_use]
    pub const fn len(self) -> usize {
        self.len as usize
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.len() == 0
    }

    #[must_use]
    pub const fn at(self, index: usize) -> DebruijnAbsolute {
        assert!(index <= self.len());

        self.start.inward(index)
    }

    #[must_use]
    pub const fn end(self) -> DebruijnAbsolute {
        self.at(self.len as usize)
    }

    #[must_use]
    pub const fn range(self) -> Range<DebruijnAbsolute> {
        self.start()..self.end()
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct DebruijnAbsolute {
    raw: u32,
}

impl DebruijnAbsolute {
    pub const ZERO: Self = Self::new(0);

    #[must_use]
    pub const fn new(v: usize) -> Self {
        Self {
            raw: usize_to_u32(v).expect("index too large"),
        }
    }

    #[must_use]
    pub const fn index(&self) -> usize {
        self.raw as usize
    }

    #[must_use]
    pub const fn inward(self, by: usize) -> Self {
        Self {
            raw: self
                .raw
                .checked_add(usize_to_u32(by).expect(OVERFLOW_ERR))
                .expect(OVERFLOW_ERR),
        }
    }

    #[must_use]
    pub const fn outward(self, by: usize) -> Self {
        Self {
            raw: self
                .raw
                .checked_sub(usize_to_u32(by).expect(OVERFLOW_ERR))
                .expect(OVERFLOW_ERR),
        }
    }

    #[must_use]
    pub const fn delta_to_outer(self, outer: DebruijnAbsolute) -> DebruijnRelative {
        let rel = self.raw.checked_sub(outer.raw).expect("index is above top");
        let rel = NonZeroU32::new(rel).expect("index cannot be top");

        DebruijnRelative { raw: rel }
    }

    #[must_use]
    pub const fn lookup_outer(self, relative: DebruijnRelative) -> DebruijnAbsolute {
        self.try_lookup_outer(relative).expect(OVERFLOW_ERR)
    }

    #[must_use]
    pub const fn try_lookup_outer(self, relative: DebruijnRelative) -> Option<DebruijnAbsolute> {
        match self.raw.checked_sub(relative.raw.get()) {
            Some(raw) => Some(DebruijnAbsolute { raw }),
            None => None,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct DebruijnRelative {
    raw: NonZeroU32,
}

impl DebruijnRelative {
    pub fn idx(self) -> NonZeroU32 {
        self.raw
    }
}

#[derive(Debug, Clone)]
#[derive_where(Default)]
pub struct DebruijnMap<T> {
    pub elems: Vec<T>,
}

impl<T> DebruijnMap<T> {
    pub fn push(&mut self, elems: impl IntoIterator<Item = T>) -> usize {
        let old_len = self.elems.len();
        self.elems.extend(elems);
        self.elems.len() - old_len
    }

    pub fn top(&self) -> DebruijnTop {
        DebruijnTop::new(self.elems.len())
    }

    pub fn try_rel_to_abs(&self, rel: DebruijnRelative) -> Option<DebruijnAbsolute> {
        self.top().try_lookup_relative(rel)
    }

    pub fn rel_to_abs(&self, rel: DebruijnRelative) -> DebruijnAbsolute {
        self.top().lookup_relative(rel)
    }

    pub fn lookup(&self, rel: DebruijnRelative) -> &T {
        &self.elems[self.rel_to_abs(rel).index()]
    }

    pub fn lookup_mut(&mut self, rel: DebruijnRelative) -> &mut T {
        let idx = self.rel_to_abs(rel).index();
        &mut self.elems[idx]
    }

    pub fn try_lookup(&self, rel: DebruijnRelative) -> Option<&T> {
        Some(&self.elems[self.try_rel_to_abs(rel)?.index()])
    }

    pub fn try_lookup_mut(&mut self, rel: DebruijnRelative) -> Option<&mut T> {
        let idx = self.try_rel_to_abs(rel)?.index();
        Some(&mut self.elems[idx])
    }

    pub fn pop(&mut self, count: usize) {
        self.elems.truncate(self.elems.len() - count);
    }
}
