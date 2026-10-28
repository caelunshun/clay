use std::{cmp::Ordering, iter, range::Range};

#[derive(Debug, Copy, Clone)]
pub struct BitRange(pub Range<u64>);

impl BitRange {
    pub fn new(range: Range<u64>) -> Self {
        Self(range)
    }

    pub fn new_usize(range: Range<usize>) -> Self {
        Self((range.start as u64..range.end as u64).into())
    }

    pub fn bit_range(&self) -> Range<u64> {
        self.0.clone()
    }

    pub fn lo_bit(&self) -> u64 {
        self.bit_range().start
    }

    pub fn hi_bit_excl(&self) -> u64 {
        self.bit_range().end
    }

    pub fn word_range(&self) -> Range<usize> {
        (self.lo_word()..self.hi_word_excl()).into()
    }

    pub fn lo_word(&self) -> usize {
        usize::try_from(self.lo_bit() / 64).unwrap()
    }

    pub fn hi_word_excl(&self) -> usize {
        usize::try_from(self.hi_bit_excl().div_ceil(64)).unwrap()
    }

    pub fn sub_range(&self, word: usize) -> Range<u32> {
        let lo = match word.cmp(&self.lo_word()) {
            Ordering::Less => return (0..0).into(),
            Ordering::Equal => (self.lo_bit() % 64) as u32,
            Ordering::Greater => 0,
        };

        let hi = match word.cmp(&self.hi_word_excl().saturating_sub(1)) {
            Ordering::Less => 64,
            Ordering::Equal => (self.hi_bit_excl() % 64) as u32,
            Ordering::Greater => return (0..0).into(),
        };

        (lo..hi).into()
    }
}

pub fn bit_mask(range: Range<u32>) -> u64 {
    let Range { start, end } = range;

    right_ones(end) & !right_ones(start)
}

pub fn right_ones(count: u32) -> u64 {
    1u64.unbounded_shl(count).wrapping_sub(1)
}

pub fn bit_iter(vec: &[u64]) -> impl Iterator<Item = usize> {
    vec.iter().enumerate().flat_map(move |(word_idx, &word)| {
        let word_base = word_idx * 64;
        bit_iter_single(word).map(move |rel_idx| word_base + rel_idx)
    })
}

pub fn bit_iter_single(mut word: u64) -> impl Iterator<Item = usize> {
    iter::from_fn(move || {
        if word == 0 {
            return None;
        }

        let idx = word.trailing_zeros();
        word ^= 1 << idx;
        Some(idx as usize)
    })
}
