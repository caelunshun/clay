use crate::{base::Session, utils::mem::MappedRc};
use std::{
    cell::RefCell,
    fmt,
    num::{NonZero, NonZeroU32},
    ops::{self, Add, AddAssign, Sub, SubAssign},
    path::PathBuf,
    rc::Rc,
};

// === Span === //

#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct FilePos(NonZeroU32);

impl fmt::Debug for FilePos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_dummy() {
            return f.write_str("<dummy>");
        }

        let file = self.file();
        write!(f, "{}:{}", file.origin(), file.pos_to_loc(*self))
    }
}

impl fmt::Display for FilePos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self, f)
    }
}

impl FilePos {
    pub const DUMMY: Self = Self(NonZero::new(u32::MAX).unwrap());

    pub const fn new(v: usize) -> Self {
        assert!(v < u32::MAX as usize); // (exclusive upper bound intentional)

        Self(NonZeroU32::new((v + 1) as u32).unwrap())
    }

    pub const fn new_u32(v: u32) -> Self {
        assert!(v != u32::MAX);

        Self(NonZeroU32::new(v + 1).unwrap())
    }

    pub const fn usize(self) -> usize {
        self.0.get() as usize - 1
    }

    pub const fn u32(self) -> u32 {
        self.0.get() - 1
    }

    pub fn is_dummy(self) -> bool {
        self == Self::DUMMY
    }

    #[must_use]
    pub fn map_usize(self, f: impl FnOnce(usize) -> usize) -> Self {
        if self.is_dummy() {
            return Self::DUMMY;
        }

        Self::new(f(self.usize()))
    }

    pub fn mutate_usize(&mut self, f: impl FnOnce(&mut usize)) {
        *self = self.map_usize(|mut v| {
            f(&mut v);
            v
        });
    }

    #[must_use]
    pub fn map_u32(self, f: impl FnOnce(u32) -> u32) -> Self {
        if self.is_dummy() {
            return Self::DUMMY;
        }

        Self::new_u32(f(self.u32()))
    }

    pub fn mutate_u32(&mut self, f: impl FnOnce(&mut u32)) {
        *self = self.map_u32(|mut v| {
            f(&mut v);
            v
        });
    }

    pub fn delta(self, other: Self) -> u32 {
        if self.is_dummy() || other.is_dummy() {
            return 0;
        }

        other.u32() - self.u32()
    }

    pub fn delta_signed(self, other: Self) -> i32 {
        if self.is_dummy() || other.is_dummy() {
            return 0;
        }

        other.u32().wrapping_sub(self.u32()) as i32
    }

    pub fn delta_usize(self, other: Self) -> usize {
        if self.is_dummy() || other.is_dummy() {
            return 0;
        }

        (other.u32() - self.u32()) as usize
    }

    pub fn file(self) -> Rc<SourceMapFile> {
        Session::fetch().source_map.file(self)
    }
}

impl Add<u32> for FilePos {
    type Output = Self;

    fn add(self, rhs: u32) -> Self::Output {
        self.map_u32(|lhs| lhs + rhs)
    }
}

impl AddAssign<u32> for FilePos {
    fn add_assign(&mut self, rhs: u32) {
        *self = *self + rhs;
    }
}

impl Sub<u32> for FilePos {
    type Output = Self;

    fn sub(self, rhs: u32) -> Self::Output {
        self.map_u32(|lhs| lhs.saturating_sub(rhs))
    }
}

impl SubAssign<u32> for FilePos {
    fn sub_assign(&mut self, rhs: u32) {
        *self = *self - rhs;
    }
}

impl Add<usize> for FilePos {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        self.map_usize(|lhs| lhs + rhs)
    }
}

impl AddAssign<usize> for FilePos {
    fn add_assign(&mut self, rhs: usize) {
        *self = *self + rhs;
    }
}

impl Sub<usize> for FilePos {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        self.map_usize(|lhs| lhs.saturating_sub(rhs))
    }
}

impl SubAssign<usize> for FilePos {
    fn sub_assign(&mut self, rhs: usize) {
        *self = *self - rhs;
    }
}

impl Default for FilePos {
    fn default() -> Self {
        Self::new(0)
    }
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct Span {
    pub lo: FilePos,
    pub hi: FilePos,
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_dummy() {
            return f.write_str("<dummy>");
        }

        let file = self.lo.file();

        let lo = file.pos_to_loc(self.lo);
        let hi = file.pos_to_loc(self.hi);

        if lo.line == hi.line {
            write!(
                f,
                "{}:{}:{}-{}",
                file.origin(),
                lo.line + 1,
                lo.column + 1,
                hi.column + 1
            )
        } else {
            write!(f, "{}:{lo}-{hi}", file.origin())
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self, f)
    }
}

impl Span {
    pub const DUMMY: Self = Self {
        lo: FilePos::DUMMY,
        hi: FilePos::DUMMY,
    };

    pub fn new(a: FilePos, b: FilePos) -> Self {
        let mut locs = [a, b];
        locs.sort();
        let [lo, hi] = locs;

        Self { lo, hi }
    }

    pub fn new_sized(lo: FilePos, size: usize) -> Self {
        Self { lo, hi: lo + size }
    }

    pub fn offset(self, offset: FilePos) -> Span {
        Span {
            lo: offset + self.lo.usize(),
            hi: offset + self.hi.usize(),
        }
    }

    pub fn shrink_to_lo(self) -> Self {
        Self {
            lo: self.lo,
            hi: self.lo,
        }
    }

    pub fn shrink_to_hi(self) -> Self {
        Self {
            lo: self.hi,
            hi: self.hi,
        }
    }

    pub fn to(self, other: Span) -> Self {
        Self::new(self.lo, other.hi)
    }

    pub fn between(self, other: Span) -> Self {
        Self::new(self.hi, other.lo)
    }

    pub fn until(self, other: Span) -> Self {
        Self::new(self.lo, other.lo)
    }

    pub fn truncate_left(self, len: usize) -> Self {
        Self::new(self.lo, (self.lo + len).min(self.hi))
    }

    pub fn interpret_byte_range(self) -> ops::Range<usize> {
        self.lo.usize()..self.hi.usize()
    }

    pub fn is_dummy(self) -> bool {
        self == Self::DUMMY
    }
}

pub trait Spanned {
    fn span(&self) -> Span;
}

// === SourceMap === //

#[derive(Debug, Clone)]
pub enum SourceFileOrigin {
    Fs(PathBuf),
    Virtual(String),
}

impl fmt::Display for SourceFileOrigin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SourceFileOrigin::Fs(path) => write!(f, "{}", path.display()),
            SourceFileOrigin::Virtual(v) => write!(f, "{v:?}"),
        }
    }
}

#[derive(Default)]
pub struct SourceMap(RefCell<SourceMapInner>);

#[derive(Default)]
struct SourceMapInner {
    files: Vec<Rc<SourceMapFile>>,
    len: FilePos,
}

impl fmt::Debug for SourceMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SourceMap").finish_non_exhaustive()
    }
}

impl SourceMap {
    pub fn create(
        &self,
        segmenter: &mut impl Segmenter,
        origin: SourceFileOrigin,
        contents: Rc<String>,
    ) -> Span {
        let mut inner = self.0.borrow_mut();
        let inner = &mut *inner;

        let lo = inner.len;
        let contents_len = contents.len();
        let segmentation = SegmentInfo::new(segmenter, &contents);

        inner.files.push(Rc::new(SourceMapFile {
            start: inner.len,
            origin,
            contents,
            segmentation,
        }));

        inner.len += contents_len + 1; // (allow EOF to be referenced)

        Span::new_sized(lo, contents_len)
    }

    pub fn file(&self, pos: FilePos) -> Rc<SourceMapFile> {
        let inner = self.0.borrow();
        let file = &inner.files[binary_search_leftwards(&inner.files, &pos, |f| f.start).unwrap()];
        assert!(file.start.delta_usize(pos) <= file.contents.len());
        file.clone()
    }
}

#[derive(Debug)]
pub struct SourceMapFile {
    start: FilePos,
    origin: SourceFileOrigin,
    contents: Rc<String>,
    segmentation: SegmentInfo,
}

impl SourceMapFile {
    pub fn start(&self) -> FilePos {
        self.start
    }

    pub fn span(&self) -> Span {
        Span::new_sized(self.start, self.contents.len())
    }

    pub fn origin(&self) -> &SourceFileOrigin {
        &self.origin
    }

    pub fn contents(&self) -> &Rc<String> {
        &self.contents
    }

    pub fn segmentation(&self) -> &SegmentInfo {
        &self.segmentation
    }

    pub fn text(&self, span: Span) -> MappedRc<String, str> {
        MappedRc::new(self.contents.clone(), |v| {
            &v[self.start.delta_usize(span.lo)..self.start.delta_usize(span.hi)]
        })
    }

    pub fn pos_to_loc(&self, pos: FilePos) -> LineCol {
        self.segmentation
            .offset_to_loc(FilePos::new_u32(self.start().delta(pos)))
    }

    pub fn loc_to_pos(&self, loc: LineCol) -> FilePos {
        self.start() + self.segmentation.loc_to_offset(loc).usize()
    }

    pub fn line_span(&self, ln_no: u32) -> Span {
        self.segmentation.line_span(ln_no).offset(self.start())
    }
}

// === Segmenter === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd, Default)]
pub struct LineCol {
    pub line: u32,
    pub column: u32,
}

impl fmt::Display for LineCol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.column + 1)
    }
}

#[derive(Debug, Clone)]
pub struct SegmentInfo {
    /// An anchor maps a `FilePos` offset to a `LineCol` pair and vice versa. Locations and
    /// positions between anchors are assumed to be non-newline single-byte single-width characters
    /// relative to the previous anchor.
    anchors: Vec<(FilePos, LineCol)>,

    /// The length of the string which was segmented.
    len: FilePos,
}

impl SegmentInfo {
    pub fn new(segmenter: &mut impl Segmenter, str: &str) -> Self {
        let mut anchors = Vec::<(FilePos, LineCol)>::new();
        let mut pos_ratchet = FilePos::new(0);

        segmenter.segment(str, |byte_pos, actual_loc| {
            let byte_pos = FilePos::new(byte_pos);

            assert!(byte_pos >= pos_ratchet);
            pos_ratchet = byte_pos;

            let (anchor_pos, anchor_loc) = anchors.last().copied().unwrap_or_default();
            let expected_loc = LineCol {
                column: anchor_loc.column + anchor_pos.delta(byte_pos),
                ..anchor_loc
            };

            if actual_loc != expected_loc {
                anchors.push((byte_pos, actual_loc));
            }
        });

        Self {
            anchors,
            len: FilePos::new(str.len()),
        }
    }

    pub fn offset_to_loc(&self, offset: FilePos) -> LineCol {
        let (anchor_pos, anchor_loc) = binary_search_leftwards(&self.anchors, &offset, |v| v.0)
            .map(|idx| self.anchors[idx])
            .unwrap_or_default();

        LineCol {
            column: anchor_loc.column + anchor_pos.delta(offset),
            ..anchor_loc
        }
    }

    fn loc_to_offset(&self, loc: LineCol) -> FilePos {
        let (anchor_pos, anchor_loc) = binary_search_leftwards(&self.anchors, &loc, |v| v.1)
            .map(|idx| self.anchors[idx])
            .unwrap_or_default();

        if anchor_loc.line == loc.line {
            anchor_pos + (loc.column - anchor_loc.column)
        } else {
            self.len
        }
    }

    pub fn line_span(&self, ln_no: u32) -> Span {
        Span {
            lo: self.loc_to_offset(LineCol {
                line: ln_no,
                column: 0,
            }),
            hi: self.loc_to_offset(LineCol {
                line: ln_no + 1,
                column: 0,
            }),
        }
    }
}

pub trait Segmenter: Sized {
    fn segment(&mut self, text: &str, sink: impl FnMut(usize, LineCol));
}

#[derive(Debug, Copy, Clone, Default)]
pub struct NaiveSegmenter;

impl Segmenter for NaiveSegmenter {
    fn segment(&mut self, text: &str, mut sink: impl FnMut(usize, LineCol)) {
        let mut pos = LineCol::default();

        for (idx, ch) in text.char_indices() {
            sink(idx, pos);

            match ch {
                '\t' => {
                    pos.column += 4;
                }
                '\r' => {
                    // (no-op)
                }
                '\n' => {
                    pos.column = 0;
                    pos.line += 1;
                }
                _ => {
                    pos.column += 1;
                }
            }
        }
    }
}

// === Utils === //

fn binary_search_leftwards<T, K>(list: &[T], key: &K, f: impl FnMut(&T) -> K) -> Option<usize>
where
    K: Ord,
{
    match list.binary_search_by_key(key, f) {
        Ok(i) => Some(i),
        Err(i) => i.checked_sub(1),
    }
}
