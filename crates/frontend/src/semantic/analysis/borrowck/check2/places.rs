use crate::{
    base::{Session, arena::HasListInterner},
    semantic::syntax::{AdtCtorOwner, MirPlace, MirPlaceElem, ResolvedFieldIdx, TyCtxt},
};
use clay_core::FastHashMap;
use index_vec::{IndexSlice, IndexVec, define_index_type};
use std::ops::Range;

#[derive(Debug, Clone)]
pub struct PlaceNumbering {
    pub place_to_range: FastHashMap<MirPlace, Range<u32>>,
    pub bit_to_place: Vec<MirPlace>,
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
                child_count: u32::MAX,
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
            mapping: &mut PlaceNumbering,
            nodes: &IndexSlice<TrieNodeIdx, [TrieNode]>,
            node: TrieNodeIdx,
        ) -> bool {
            let node = &nodes[node];

            let first_field = mapping.bit_to_place.len() as u32;

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
            if let Some(place) = node.mention
                && !structural_liveness
            {
                mapping.bit_to_place.push(place);

                // Our liveness is now structural again because we have a bit!
                structural_liveness = true;
            }

            if let Some(place) = node.mention {
                let next_field = mapping.bit_to_place.len() as u32;

                mapping
                    .place_to_range
                    .insert(place, first_field..next_field);
            }

            structural_liveness
        }

        let mut mapping = PlaceNumbering {
            place_to_range: FastHashMap::default(),
            bit_to_place: Vec::new(),
        };

        for idx in 0..self.local_count {
            populate(&mut mapping, &self.nodes, TrieNodeIdx::from_usize(idx));
        }

        mapping
    }
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
