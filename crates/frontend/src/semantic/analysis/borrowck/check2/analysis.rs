use crate::{
    base::Session,
    semantic::syntax::{
        MirBody, MirBodyDirection, MirPlace, MirPlaceElem, ResolvedFieldIdx, TyCtxt,
    },
};
use clay_core::FastHashMap;

// === PlaceSet Lattice === //

pub struct PlaceSetMapping {
    mapping: FastHashMap<MirPlace, PlaceSetRange>,
}

struct PlaceSetRange {
    base_field: u32,
    child_fields: u32,
}

impl PlaceSetMapping {
    // TODO
}

pub struct PlaceSetMappingBuilder {
    nodes: Vec<TrieNode>,
}

struct TrieNode {
    first_child: u32,
    child_count: u32,
    place: Option<MirPlace>,
}

impl PlaceSetMappingBuilder {
    pub fn new(local_count: usize) -> Self {
        Self {
            nodes: (0..local_count)
                .map(|_| TrieNode {
                    first_child: u32::MAX,
                    child_count: u32::MAX,
                    place: None,
                })
                .collect(),
        }
    }

    pub fn add(&mut self, s: &Session, place: MirPlace) {
        let mut curr = place.local.index();

        for part in place.projections.r(s) {
            match part {
                MirPlaceElem::DerefPtr => {
                    break;
                }
                MirPlaceElem::Field(ResolvedFieldIdx::Adt(adt, field_idx)) => todo!(),
                MirPlaceElem::Field(ResolvedFieldIdx::Tuple(field_idx)) => todo!(),
            }
        }
    }

    fn finish(&self) -> PlaceSetMapping {
        todo!()
    }
}
