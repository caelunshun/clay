use derive_where::derive_where;
use std::{cmp::Ordering, fmt::Debug, slice};

// === IterEither === //

#[derive(Clone)]
pub enum IterEither<L, R> {
    Left(L),
    Right(R),
}

impl<T, L, R> ExactSizeIterator for IterEither<L, R>
where
    L: ExactSizeIterator<Item = T>,
    R: ExactSizeIterator<Item = T>,
{
}

impl<T, L, R> Iterator for IterEither<L, R>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            IterEither::Left(v) => v.next(),
            IterEither::Right(v) => v.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            IterEither::Left(v) => v.size_hint(),
            IterEither::Right(v) => v.size_hint(),
        }
    }
}

// === BinarySeekIterator === //

pub trait BinarySeekIterator: Iterator {
    fn seek_geq_with(&mut self, cmp: impl FnMut(&Self::Item) -> Ordering);

    fn seek_geq(&mut self, min_eq: &Self::Item)
    where
        Self::Item: Ord,
    {
        self.seek_geq_with(|other| min_eq.cmp(other));
    }

    fn next_geq_with(&mut self, cmp: impl FnMut(&Self::Item) -> Ordering) -> Option<Self::Item> {
        self.seek_geq_with(cmp);
        self.next()
    }

    fn next_geq(&mut self, min_eq: &Self::Item) -> Option<Self::Item>
    where
        Self::Item: Ord,
    {
        self.seek_geq(min_eq);
        self.next()
    }
}

impl<T: Ord> BinarySeekIterator for slice::Iter<'_, T> {
    fn seek_geq_with(&mut self, mut cmp: impl FnMut(&Self::Item) -> Ordering) {
        while self.as_slice().first().is_some_and(|v| cmp(&v).is_gt()) {
            self.next();
        }

        // TODO: Use the optimized form.
        // if self.as_slice().is_empty() {
        //     return;
        // }
        //
        // // Handle small-seek fast-path
        // if let Some(first) = self.as_slice().first() {
        //     if cmp(&first).is_le() {
        //         // `min_eq <= next`
        //         return;
        //     }
        //
        //     self.next();
        //
        //     if let Some(next) = self.as_slice().first()
        //         && cmp(&next).is_le()
        //     {
        //         return;
        //     }
        // }
        //
        // // Perform a binary search to find our seek location.
        // let (Ok(idx) | Err(idx)) = self.as_slice().binary_search_by(|v| cmp(&v).reverse());
        //
        // debug_assert_ne!(idx, 0);
        // self.nth(idx - 1);
    }
}

// === UnionIsectIter === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum UnionIsectOp {
    Union,
    Intersect,
}

// Builder
#[derive_where(Default)]
pub struct UnionIsectBuilder<I: Iterator> {
    parts: Vec<UnionIsectPart<I>>,
    op_builder_stack: Vec<(UnionIsectOp, usize)>,
}

impl<I: Iterator> UnionIsectBuilder<I> {
    pub fn push_op(&mut self, kind: UnionIsectOp) {
        self.op_builder_stack.push((kind, self.parts.len()));
    }

    pub fn push_iter(&mut self, iter: I) {
        debug_assert!(!self.op_builder_stack.is_empty());

        self.parts.push(UnionIsectPart {
            kind: UnionIsectPartKind::Source(iter),
            next_elem: None,
            fused: false,
        });
    }

    pub fn pop_op(&mut self) {
        let (kind, first_iter) = self.op_builder_stack.pop().unwrap();

        match self.parts.len() - first_iter {
            0 => {
                self.parts.push(UnionIsectPart {
                    kind: UnionIsectPartKind::Empty,
                    next_elem: None,
                    fused: false,
                });
            }
            1 => {
                // (ignore)
            }
            _ => {
                self.parts.push(UnionIsectPart {
                    kind: UnionIsectPartKind::Operation {
                        kind,
                        first_iter_idx: first_iter,
                    },
                    next_elem: None,
                    fused: false,
                });
            }
        }
    }

    pub fn finish(self) -> UnionIsectIter<I> {
        debug_assert!(self.op_builder_stack.is_empty());

        UnionIsectIter { parts: self.parts }
    }
}

// Iterator
#[derive_where(Default)]
pub struct UnionIsectIter<I: Iterator> {
    parts: Vec<UnionIsectPart<I>>,
}

struct UnionIsectPart<I: Iterator> {
    kind: UnionIsectPartKind<I>,
    next_elem: Option<I::Item>,
    fused: bool,
}

enum UnionIsectPartKind<I> {
    Source(I),
    Empty,
    Operation {
        kind: UnionIsectOp,
        first_iter_idx: usize,
    },
}

impl<I> UnionIsectIter<I>
where
    I: BinarySeekIterator<Item: Ord>,
{
    fn step(&mut self, own_idx: usize) {
        let part = &mut self.parts[own_idx];

        if part.next_elem.is_some() {
            return;
        }

        if part.fused {
            return;
        }

        match part.kind {
            UnionIsectPartKind::Source(ref mut src) => {
                part.next_elem = src.next();
            }
            UnionIsectPartKind::Empty => {
                // (leave the `next_elem` empty)
            }
            UnionIsectPartKind::Operation {
                kind: UnionIsectOp::Union,
                first_iter_idx,
            } => {
                let mut min_elem = None::<usize>;

                // Step all iterators and look for the minimum element.
                let mut next_iter_idx = own_idx.checked_sub(1);

                while let Some(curr_iter_idx) = next_iter_idx
                    && curr_iter_idx >= first_iter_idx
                {
                    match self.parts[curr_iter_idx].kind {
                        UnionIsectPartKind::Source(_) | UnionIsectPartKind::Empty => {
                            next_iter_idx = curr_iter_idx.checked_sub(1);
                        }
                        UnionIsectPartKind::Operation { first_iter_idx, .. } => {
                            next_iter_idx = first_iter_idx.checked_sub(1);
                        }
                    }

                    self.step(curr_iter_idx);

                    let Some(iter_elem) = &self.parts[curr_iter_idx].next_elem else {
                        continue;
                    };

                    if min_elem.is_none_or(|min_idx| {
                        iter_elem < self.parts[min_idx].next_elem.as_ref().unwrap()
                    }) {
                        min_elem = Some(curr_iter_idx);
                    }
                }

                // Take out the minimum element.
                if let Some(min_elem) = min_elem {
                    let elem = self.parts[min_elem].next_elem.take().unwrap();

                    // Eat all duplicates of the element.
                    let mut next_iter_idx = own_idx.checked_sub(1);

                    while let Some(curr_iter_idx) = next_iter_idx
                        && curr_iter_idx >= first_iter_idx
                    {
                        match self.parts[curr_iter_idx].kind {
                            UnionIsectPartKind::Source(_) | UnionIsectPartKind::Empty => {
                                next_iter_idx = curr_iter_idx.checked_sub(1);
                            }
                            UnionIsectPartKind::Operation { first_iter_idx, .. } => {
                                next_iter_idx = first_iter_idx.checked_sub(1);
                            }
                        }

                        while let Some(iter_elem) = &self.parts[curr_iter_idx].next_elem
                            && iter_elem == &elem
                        {
                            self.parts[curr_iter_idx].next_elem = None;
                            self.step(curr_iter_idx);
                        }
                    }

                    // Yield the element.
                    self.parts[own_idx].next_elem = Some(elem);
                }
            }
            UnionIsectPartKind::Operation {
                kind: UnionIsectOp::Intersect,
                first_iter_idx,
            } => {
                'intersect: loop {
                    // Step all iterators and look for the maximum element.
                    let mut max_elem = None::<usize>;
                    let mut all_equal = true;

                    let mut next_iter_idx = own_idx.checked_sub(1);

                    while let Some(curr_iter_idx) = next_iter_idx
                        && curr_iter_idx >= first_iter_idx
                    {
                        match self.parts[curr_iter_idx].kind {
                            UnionIsectPartKind::Source(_) | UnionIsectPartKind::Empty => {
                                next_iter_idx = curr_iter_idx.checked_sub(1);
                            }
                            UnionIsectPartKind::Operation { first_iter_idx, .. } => {
                                next_iter_idx = first_iter_idx.checked_sub(1);
                            }
                        }

                        self.step(curr_iter_idx);

                        let Some(iter_elem) = &self.parts[curr_iter_idx].next_elem else {
                            break 'intersect;
                        };

                        if max_elem.is_none_or(|max_idx| {
                            let max_elem = self.parts[max_idx].next_elem.as_ref().unwrap();

                            let cmp = iter_elem.cmp(max_elem);

                            if cmp.is_ne() {
                                all_equal = false;
                            }

                            cmp.is_ge()
                        }) {
                            max_elem = Some(curr_iter_idx);
                        }
                    }

                    let max_elem = max_elem.unwrap();

                    // If all elements are equal, consume from each iterator and advance the cursor.
                    if all_equal {
                        let next_elem = self.parts[max_elem].next_elem.take().unwrap();

                        let mut next_iter_idx = own_idx.checked_sub(1);

                        while let Some(curr_iter_idx) = next_iter_idx
                            && curr_iter_idx >= first_iter_idx
                        {
                            match self.parts[curr_iter_idx].kind {
                                UnionIsectPartKind::Source(_) | UnionIsectPartKind::Empty => {
                                    next_iter_idx = curr_iter_idx.checked_sub(1);
                                }
                                UnionIsectPartKind::Operation { first_iter_idx, .. } => {
                                    next_iter_idx = first_iter_idx.checked_sub(1);
                                }
                            }

                            self.parts[curr_iter_idx].next_elem = None;
                        }

                        self.parts[own_idx].next_elem = Some(next_elem);
                        break;
                    }

                    // Otherwise, advance all source iterators to the maximum seen element.
                    for iter_idx in first_iter_idx..own_idx {
                        if max_elem == iter_idx {
                            continue;
                        }

                        let Ok([iter, max_elem]) =
                            self.parts.get_disjoint_mut([iter_idx, max_elem])
                        else {
                            unreachable!()
                        };

                        let max_elem = max_elem.next_elem.as_ref().unwrap();

                        if iter.next_elem.as_ref().is_none_or(|v| v >= max_elem) {
                            continue;
                        }

                        iter.next_elem = None;

                        let UnionIsectPartKind::Source(iter) = &mut iter.kind else {
                            continue;
                        };

                        iter.seek_geq(max_elem);
                    }
                }
            }
        }

        let part = &mut self.parts[own_idx];
        part.fused = part.next_elem.is_none();
    }
}

impl<I> Iterator for UnionIsectIter<I>
where
    I: BinarySeekIterator<Item: Ord>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let part_count = self.parts.len();

        if part_count == 0 {
            return None;
        }

        self.step(part_count - 1);
        self.parts.last_mut().unwrap().next_elem.take()
    }
}

// === Tests === //

#[cfg(test)]
mod tests {
    use super::*;
    use bumpalo::Bump;
    use std::collections::BTreeSet;

    // === Model === //

    #[derive_where(Default)]
    struct Model<T> {
        stack: Vec<(UnionIsectOp, Option<BTreeSet<T>>)>,
    }

    impl<T: Ord> Model<T> {
        pub fn push_op(&mut self, kind: UnionIsectOp) {
            self.stack.push((kind, None));
        }

        pub fn push_iter(&mut self, iter: impl IntoIterator<Item = T>) {
            let (op, head) = self.stack.last_mut().unwrap();

            match op {
                UnionIsectOp::Union => {
                    head.get_or_insert_default().extend(iter);
                }
                UnionIsectOp::Intersect => {
                    let iter = BTreeSet::from_iter(iter);

                    if let Some(head) = head {
                        head.retain(|other| iter.contains(other));
                    } else {
                        *head = Some(iter);
                    }
                }
            }
        }

        pub fn pop_op(&mut self) {
            if self.stack.len() == 1 {
                return;
            }

            let (_src_op, src) = self.stack.pop().unwrap();
            let src = src.unwrap_or_default();

            let (onto_op, onto) = self.stack.last_mut().unwrap();

            match onto_op {
                UnionIsectOp::Union => {
                    onto.get_or_insert_default().extend(src);
                }
                UnionIsectOp::Intersect => {
                    if let Some(onto) = onto {
                        onto.retain(|other| src.contains(other));
                    } else {
                        *onto = Some(src);
                    }
                }
            }
        }

        pub fn finish(self) -> BTreeSet<T> {
            debug_assert_eq!(self.stack.len(), 1);

            self.stack.into_iter().next().unwrap().1.unwrap_or_default()
        }
    }

    // === Validator === //

    #[derive(Default)]
    struct Validator<'a> {
        model: Model<u32>,
        actual: UnionIsectBuilder<slice::Iter<'a, u32>>,
    }

    impl<'a> Validator<'a> {
        pub fn push_op(&mut self, kind: UnionIsectOp) {
            self.actual.push_op(kind);
            self.model.push_op(kind);
        }

        pub fn push_iter(&mut self, iter: &'a [u32]) {
            self.actual.push_iter(iter.iter());
            self.model.push_iter(iter.iter().copied());
        }

        pub fn pop_op(&mut self) {
            self.actual.pop_op();
            self.model.pop_op();
        }

        pub fn finish(self) {
            let actual = self.actual.finish().copied().collect::<Vec<_>>();
            let expected = self.model.finish().into_iter().collect::<Vec<_>>();

            assert_eq!(actual, expected);
        }
    }

    // === Tests === //

    #[test]
    fn empty_union() {
        let mut validator = Validator::default();

        validator.push_op(UnionIsectOp::Union);
        validator.push_iter(&[1, 3, 4, 4, 5]);
        validator.push_iter(&[]);
        validator.pop_op();
        validator.finish();
    }

    #[test]
    fn simple_union() {
        let mut validator = Validator::default();

        validator.push_op(UnionIsectOp::Union);
        validator.push_iter(&[1, 3, 4, 4, 5]);
        validator.push_iter(&[1, 2, 4]);
        validator.pop_op();
    }

    #[test]
    fn simple_intersect() {
        let mut validator = Validator::default();

        validator.push_op(UnionIsectOp::Intersect);
        validator.push_iter(&[1, 3, 4, 4, 5]);
        validator.push_iter(&[1, 2, 4]);
        validator.pop_op();
    }

    #[test]
    fn prop_test() {
        fastrand::seed(4);

        for _ in 0..50_000 {
            let bump = Bump::new();

            fn fill_random<'b>(bump: &'b Bump, validator: &mut Validator<'b>, depth: u32) {
                let indent = (0..depth).map(|_| "  ").collect::<Vec<_>>().join("");

                match fastrand::u8(0..=if depth <= 5 { 7 } else { 5 }) {
                    0..=5 => {
                        let slice = bump.alloc_slice_copy(
                            &(0..fastrand::u32(0..20))
                                .filter(|_| fastrand::bool())
                                .collect::<Vec<_>>(),
                        );

                        eprintln!("{indent}validator.push_iter(&{slice:?});");
                        validator.push_iter(slice);
                    }
                    v @ (6 | 7) => {
                        validator.push_op(match v {
                            6 => {
                                eprintln!("{indent}validator.push_op(UnionIsectOp::Union);");
                                UnionIsectOp::Union
                            }
                            7 => {
                                eprintln!("{indent}validator.push_op(UnionIsectOp::Intersect);");
                                UnionIsectOp::Intersect
                            }
                            _ => unreachable!(),
                        });

                        for _ in 0..fastrand::u8(0..=4) {
                            fill_random(bump, validator, depth + 1);
                        }

                        eprintln!("{indent}validator.pop_op();");
                        validator.pop_op();
                    }
                    _ => unreachable!(),
                }
            }

            eprintln!("\n// Seed {}", fastrand::get_seed());

            eprintln!("let mut validator = Validator::default();");
            let mut validator = Validator::default();

            eprintln!("validator.push_op(UnionIsectOp::Union);");
            validator.push_op(UnionIsectOp::Union);

            fill_random(&bump, &mut validator, 1);

            eprintln!("validator.pop_op();");
            validator.pop_op();

            eprintln!("validator.finish();");
            validator.finish();
        }
    }

    #[test]
    fn weird_case() {
        let mut validator = Validator::default();
        validator.push_op(UnionIsectOp::Intersect);
        {
            validator.push_op(UnionIsectOp::Union);
            {
                validator.push_iter(&[1, 3]);
                validator.push_iter(&[1]);
            }
            validator.pop_op();
            validator.push_iter(&[2, 3]);
        }
        validator.pop_op();
        validator.finish();
    }
}
