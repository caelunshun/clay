use crate::{
    base::{Session, arena::HasListInterner},
    semantic::syntax::{
        AdtCtorOwner, MirBody, MirBodyDirection, MirPlace, MirPlaceElem, MirPrettyFmt,
        ResolvedFieldIdx, TraverseMentions, TyCtxt,
    },
    utils::{
        format::DebugAsDisplay,
        lang::RangeExt,
        mem::{BitRange, bit_iter, bit_mask},
    },
};
use clay_core::FastHashMap;
use index_vec::{IndexSlice, IndexVec, define_index_type};
use smallvec::SmallVec;
use std::{fmt, range::Range};

// === PlaceNumbering === //

define_index_type! {
    pub struct AtomicPlaceIdx = u32;
}

#[derive(Debug, Clone)]
pub struct PlaceNumbering {
    pub place_to_range: FastHashMap<MirPlace, Range<AtomicPlaceIdx>>,
    pub bit_to_atomic_place: IndexVec<AtomicPlaceIdx, MirPlace>,
}

#[derive(Clone)]
pub struct PlaceNumberingBuilder {
    nodes: IndexVec<TrieNodeIdx, TrieNode>,
    local_count: usize,
}

define_index_type! {
    struct TrieNodeIdx = u32;
}

#[derive(Clone)]
struct TrieNode {
    first_child: TrieNodeIdx,
    child_count: u32,
    mention: Option<MirPlace>,
}

impl PlaceNumberingBuilder {
    pub fn new(local_count: usize) -> Self {
        Self {
            nodes: (0..local_count)
                .map(|_| TrieNode {
                    first_child: TrieNodeIdx::from_raw(u32::MAX),
                    child_count: 0,
                    mention: None,
                })
                .collect(),
            local_count,
        }
    }

    fn ensure_child(
        &mut self,
        node_idx: TrieNodeIdx,
        child_idx: usize,
        child_len: usize,
    ) -> TrieNodeIdx {
        let TrieNode {
            mut first_child,
            mut child_count,
            ..
        } = self.nodes[node_idx];

        if first_child.raw() == u32::MAX {
            first_child = TrieNodeIdx::from_usize(self.nodes.len());
            child_count = child_len as u32;

            self.nodes[node_idx].first_child = first_child;
            self.nodes[node_idx].child_count = child_count;

            self.nodes.extend((0..child_len).map(|_| TrieNode {
                first_child: TrieNodeIdx::from_raw(u32::MAX),
                child_count: 0,
                mention: None,
            }));
        }

        assert_eq!(child_count, child_len as u32);
        assert!(child_idx < child_len);

        return TrieNodeIdx::from_usize(first_child.index() + child_idx);
    }

    pub fn mention(&mut self, s: &Session, place: MirPlace) {
        assert!(place.local < self.local_count);

        let mut curr = TrieNodeIdx::from_usize(place.local.index());

        for &part in place.projections.r(s) {
            match part {
                MirPlaceElem::Field(ResolvedFieldIdx::Adt(adt, field_idx)) => {
                    match adt.r(s).owner {
                        AdtCtorOwner::Struct(_) => {
                            // (no-op)
                        }
                        AdtCtorOwner::EnumVariant(adt) => {
                            curr = self.ensure_child(
                                curr,
                                adt.r(s).idx.index(),
                                adt.r(s).owner.r(s).variants.len(),
                            );
                        }
                    }

                    curr = self.ensure_child(curr, field_idx.index(), adt.r(s).fields.len());
                }
                MirPlaceElem::Field(ResolvedFieldIdx::Tuple {
                    field_idx,
                    max_elems,
                }) => {
                    curr = self.ensure_child(curr, field_idx as usize, max_elems as usize);
                }
                MirPlaceElem::DerefPtr => {
                    unreachable!("direct places cannot contain {part:?}");
                }
            }
        }

        let mention = &mut self.nodes[curr].mention;
        assert!(mention.is_none_or(|v| v == place));
        *mention = Some(place);
    }

    pub fn finish(&self) -> PlaceNumbering {
        // Reserves bits for all child places of the specified `node`, returning `true` if the
        // node's liveness can be determined by looking at its allocated bit range.
        //
        // ```
        // * A (place mentioned)          <-- NO bit allocated ;     structurally determined
        // |-- B (place mentioned)        <-- NO bit allocated ;     structurally determined
        //     |-- C (place mentioned)    <--    bit allocated ;     structurally determined
        //     |-- D (place mentioned)    <--    bit allocated ;     structurally determined
        // |-- E (place mentioned)        <--    bit allocated ;     structurally determined
        //     |--F                       <-- NO bit allocated ; NOT structurally determined
        //        |-- G (place mentioned) <--    bit allocated ;     structurally determined
        //        |-- H                   <-- NO bit allocated ; NOT structurally determined
        // ```
        //
        // This is necessary for correctness since we would like to...
        //
        // - initialize a place by initializing all its sub-components
        // - but not accidentally have a place be initialized by initializing only its mentioned
        //   sub-components
        //
        fn populate(
            numbering: &mut PlaceNumbering,
            nodes: &IndexSlice<TrieNodeIdx, [TrieNode]>,
            node: TrieNodeIdx,
        ) -> bool {
            let node = &nodes[node];

            let first_field = AtomicPlaceIdx::from_usize(numbering.bit_to_atomic_place.len());

            // A place is structurally live if all its children are structurally live.
            let mut structural_liveness = true;

            for child_idx in 0..node.child_count {
                structural_liveness &= populate(
                    numbering,
                    nodes,
                    TrieNodeIdx::from_usize(node.first_child.index() + child_idx as usize),
                );
            }

            // If a not has no children, it cannot be structurally live because which bits would we
            // look at?
            if node.child_count == 0 {
                structural_liveness = false;
            }

            // If an alias was requested and our liveness cannot be structurally determined,
            // allocate a bit!
            if let Some(place) = node.mention
                && !structural_liveness
            {
                numbering.bit_to_atomic_place.push(place);

                // Our liveness is now structural again because we have a bit!
                structural_liveness = true;
            }

            if let Some(place) = node.mention {
                let next_field = AtomicPlaceIdx::from_usize(numbering.bit_to_atomic_place.len());

                numbering
                    .place_to_range
                    .insert(place, (first_field..next_field).into());
            }

            structural_liveness
        }

        let mut numbering = PlaceNumbering {
            place_to_range: FastHashMap::default(),
            bit_to_atomic_place: IndexVec::new(),
        };

        for idx in 0..self.local_count {
            populate(&mut numbering, &self.nodes, TrieNodeIdx::from_usize(idx));
        }

        numbering
    }
}

pub fn number_places_in_body(tcx: &TyCtxt, body: &MirBody) -> PlaceNumbering {
    let s = &tcx.session;
    let mut builder = PlaceNumberingBuilder::new(body.locals.len());

    for local in body.arg_locals() {
        builder.mention(s, MirPlace::new(tcx, local, []));
    }

    for block in body.blocks() {
        for stmt in block.stmts(MirBodyDirection::Forwards) {
            cbit::cbit! {
                for mention in stmt.kind().iter_mentions(tcx) {
                    builder.mention(s, truncate_place_to_direct(tcx, mention.place));
                }
            }
        }

        cbit::cbit! {
            for mention in block.terminator_kind().iter_mentions(tcx) {
                builder.mention(s, truncate_place_to_direct(tcx, mention.place));
            }
        }
    }

    builder.finish()
}

pub fn truncate_place_to_direct(tcx: &TyCtxt, place: MirPlace) -> MirPlace {
    let s = &tcx.session;

    MirPlace {
        local: place.local,
        projections: tcx.intern_list(
            &place
                .projections
                .r(s)
                .iter()
                .copied()
                .take_while(|v| match v {
                    MirPlaceElem::DerefPtr => false,
                    MirPlaceElem::Field(_) => true,
                })
                .collect::<Vec<_>>(),
        ),
    }
}

// === PlaceSet === //

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct PlaceSet {
    bits: SmallVec<[u64; 3]>,
}

impl PlaceSet {
    pub fn pretty<'a>(
        &'a self,
        mir_fmt: &'a MirPrettyFmt,
        numbering: &'a PlaceNumbering,
    ) -> PlaceSetPrettyFmt<'a> {
        PlaceSetPrettyFmt {
            mir_fmt,
            set: self,
            numbering,
        }
    }

    pub fn clear(&mut self) {
        self.bits.clear();
    }

    pub fn fill(&mut self, numbering: &PlaceNumbering) {
        self.clear();
        self.add_range(
            Range::from(0..numbering.bit_to_atomic_place.len()).map(AtomicPlaceIdx::from_usize),
        );
    }

    pub fn add_one(&mut self, idx: AtomicPlaceIdx) {
        self.add_range((idx..(idx + 1)).into());
    }

    pub fn add_range(&mut self, range: Range<AtomicPlaceIdx>) {
        let bits = BitRange::new_usize(range.map(|v| v.index()));

        if bits.hi_word_excl() > self.bits.len() {
            self.bits.resize(bits.hi_word_excl(), 0);
        }

        for word in bits.word_range() {
            let sub = bits.sub_range(word);

            self.bits[word] |= bit_mask(sub);
        }
    }

    pub fn add_place(&mut self, numbering: &PlaceNumbering, place: MirPlace) {
        self.add_range(numbering.place_to_range[&place]);
    }

    pub fn remove_one(&mut self, idx: AtomicPlaceIdx) {
        self.remove_range((idx..(idx + 1)).into());
    }

    pub fn remove_range(&mut self, range: Range<AtomicPlaceIdx>) {
        let bits = BitRange::new_usize(range.map(|v| v.index()));

        if bits.hi_word_excl() > self.bits.len() {
            self.bits.resize(bits.hi_word_excl(), 0);
        }

        for word in bits.word_range() {
            let sub = bits.sub_range(word);

            self.bits[word] &= !bit_mask(sub);
        }
    }

    pub fn remove_place(&mut self, numbering: &PlaceNumbering, place: MirPlace) {
        self.remove_range(numbering.place_to_range[&place]);
    }

    pub fn has_one(&self, idx: AtomicPlaceIdx) -> bool {
        self.has_range((idx..(idx + 1)).into())
    }

    pub fn has_range(&self, range: Range<AtomicPlaceIdx>) -> bool {
        let bits = BitRange::new_usize(range.map(|v| v.index()));

        if bits.hi_word_excl() > self.bits.len() {
            return false;
        }

        bits.word_range().into_iter().all(|word| {
            let mask = bit_mask(bits.sub_range(word));
            self.bits[word] & mask == mask
        })
    }

    pub fn has_place(&self, numbering: &PlaceNumbering, place: MirPlace) -> bool {
        self.has_range(numbering.place_to_range[&place])
    }

    pub fn union(&mut self, other: &Self) {
        if other.bits.len() > self.bits.len() {
            self.bits.resize(other.bits.len(), 0);
        }

        for (lhs, &rhs) in self.bits.iter_mut().zip(&other.bits) {
            *lhs |= rhs;
        }
    }

    pub fn intersect(&mut self, other: &Self) {
        if other.bits.len() > self.bits.len() {
            self.bits.resize(other.bits.len(), 0);
        }

        for (lhs, &rhs) in self.bits.iter_mut().zip(&other.bits) {
            *lhs &= rhs;
        }
    }

    pub fn removed(&mut self, other: &Self) {
        if other.bits.len() > self.bits.len() {
            self.bits.resize(other.bits.len(), 0);
        }

        for (lhs, &rhs) in self.bits.iter_mut().zip(&other.bits) {
            *lhs &= !rhs;
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = AtomicPlaceIdx> {
        bit_iter(&self.bits).map(AtomicPlaceIdx::from_usize)
    }
}

#[derive(Copy, Clone)]
pub struct PlaceSetPrettyFmt<'a> {
    pub mir_fmt: &'a MirPrettyFmt<'a>,
    pub set: &'a PlaceSet,
    pub numbering: &'a PlaceNumbering,
}

impl fmt::Display for PlaceSetPrettyFmt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_list();

        for place in self.numbering.place_to_range.keys().copied() {
            if !self.set.has_place(self.numbering, place) {
                continue;
            }

            f.entry(&DebugAsDisplay(self.mir_fmt.place(place)));
        }

        f.finish()
    }
}
