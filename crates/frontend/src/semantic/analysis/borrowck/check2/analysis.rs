use crate::{
    base::Session,
    semantic::syntax::{AdtCtorOwner, MirPlace, MirPlaceElem, ResolvedFieldIdx},
    utils::mem::{BitRange, bit_mask},
};
use clay_core::{FastHashMap, FastHashSet};
use index_vec::{IndexSlice, IndexVec, define_index_type};
use smallvec::SmallVec;
use std::ops::Range;

// === PlaceSet Lattice === //

#[derive(Debug, Clone)]
pub struct PlaceIdMap {
    pub places: FastHashMap<MirPlace, Range<u32>>,
    pub bit_count: u32,
}

#[derive(Clone)]
pub struct PlaceIdMapBuilder {
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
    aliases: FastHashSet<MirPlace>,
}

impl PlaceIdMapBuilder {
    pub fn new(local_count: usize) -> Self {
        Self {
            nodes: (0..local_count)
                .map(|_| TrieNode {
                    first_child: TrieNodeIdx::from_raw(u32::MAX),
                    child_count: 0,
                    aliases: FastHashSet::default(),
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
                child_count: u32::MAX,
                aliases: FastHashSet::default(),
            }));
        }

        assert_eq!(child_count, child_len as u32);
        assert!(child_idx < child_len);

        return TrieNodeIdx::from_usize(first_child.index() + child_idx);
    }

    pub fn add(&mut self, s: &Session, place: MirPlace) {
        assert!(place.local < self.local_count);

        let mut curr = TrieNodeIdx::from_usize(place.local.index());

        for &part in place.projections.r(s) {
            match part {
                MirPlaceElem::DerefPtr => {
                    break;
                }
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
            }
        }

        self.nodes[curr].aliases.insert(place);
    }

    fn finish(&self) -> PlaceIdMap {
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
            mapping: &mut PlaceIdMap,
            nodes: &IndexSlice<TrieNodeIdx, [TrieNode]>,
            node: TrieNodeIdx,
        ) -> bool {
            let node = &nodes[node];

            let first_field = mapping.bit_count;

            // A place is structurally live if all its children are structurally live.
            let mut structural_liveness = true;

            for child_idx in 0..node.child_count {
                structural_liveness &= populate(
                    mapping,
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
            if !node.aliases.is_empty() && !structural_liveness {
                mapping.bit_count += 1;

                // Our liveness is now structural again because we have a bit!
                structural_liveness = true;
            }

            for &alias in &node.aliases {
                mapping.places.insert(alias, first_field..mapping.bit_count);
            }

            structural_liveness
        }

        let mut mapping = PlaceIdMap {
            bit_count: 0,
            places: FastHashMap::default(),
        };

        for idx in 0..self.local_count {
            populate(&mut mapping, &self.nodes, TrieNodeIdx::from_usize(idx));
        }

        mapping
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct PlaceSet {
    bits: SmallVec<[u64; 3]>,
}

impl PlaceSet {
    pub fn add(&mut self, mapping: &PlaceIdMap, place: MirPlace) {
        let bits = BitRange::new_u32(mapping.places[&place].clone());

        if bits.hi_word_excl() > self.bits.len() {
            self.bits.resize(bits.hi_word_excl(), 0);
        }

        for word in bits.word_range() {
            let sub = bits.sub_range(word);

            self.bits[word] |= bit_mask(sub);
        }
    }

    pub fn remove(&mut self, mapping: &PlaceIdMap, place: MirPlace) {
        let bits = BitRange::new_u32(mapping.places[&place].clone());

        if bits.hi_word_excl() > self.bits.len() {
            self.bits.resize(bits.hi_word_excl(), 0);
        }

        for word in bits.word_range() {
            let sub = bits.sub_range(word);

            self.bits[word] &= !bit_mask(sub);
        }
    }

    pub fn has(&self, mapping: &PlaceIdMap, place: MirPlace) -> bool {
        let bits = BitRange::new_u32(mapping.places[&place].clone());

        if bits.hi_word_excl() > self.bits.len() {
            return false;
        }

        bits.word_range().all(|word| {
            let mask = bit_mask(bits.sub_range(word));
            self.bits[word] & mask == mask
        })
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
}
