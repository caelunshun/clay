use crate::{
    semantic::{
        analysis::borrowck::check2::{
            dataflow::{BackwardsDataflowAnalysis, DataflowOutput},
            place_map::PlaceIdMap,
        },
        syntax::{MirBlockIdx, MirBody, MirPlace, MirStmtIdx, TyCtxt},
    },
    utils::mem::{BitRange, bit_mask},
};
use smallvec::SmallVec;

// === PlaceSet === //

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct PlaceSet {
    bits: SmallVec<[u64; 3]>,
}

impl PlaceSet {
    pub fn add(&mut self, mapping: &PlaceIdMap, place: MirPlace) {
        let bits = BitRange::new_u32(mapping.place_to_range[&place].clone());

        if bits.hi_word_excl() > self.bits.len() {
            self.bits.resize(bits.hi_word_excl(), 0);
        }

        for word in bits.word_range() {
            let sub = bits.sub_range(word);

            self.bits[word] |= bit_mask(sub);
        }
    }

    pub fn remove(&mut self, mapping: &PlaceIdMap, place: MirPlace) {
        let bits = BitRange::new_u32(mapping.place_to_range[&place].clone());

        if bits.hi_word_excl() > self.bits.len() {
            self.bits.resize(bits.hi_word_excl(), 0);
        }

        for word in bits.word_range() {
            let sub = bits.sub_range(word);

            self.bits[word] &= !bit_mask(sub);
        }
    }

    pub fn has(&self, mapping: &PlaceIdMap, place: MirPlace) -> bool {
        let bits = BitRange::new_u32(mapping.place_to_range[&place].clone());

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

// === LivenessAnalysis === //

pub struct LivenessAnalysis<'g> {
    tcx: &'g TyCtxt,
    body: &'g MirBody,
    id_map: &'g PlaceIdMap,
}

impl<'g> BackwardsDataflowAnalysis<'g> for LivenessAnalysis<'g> {
    type Lattice = PlaceSet;

    fn body(&self) -> &'g MirBody {
        self.body
    }

    fn init_effect(&mut self) -> Self::Lattice {
        PlaceSet::default()
    }

    fn trans_stmt(
        &mut self,
        idx: MirStmtIdx,
        input: &Self::Lattice,
        output: &mut DataflowOutput<Self::Lattice>,
    ) {
        todo!()
    }

    fn trans_terminator(
        &mut self,
        idx: MirBlockIdx,
        inputs: &[&Self::Lattice],
        outputs: &mut DataflowOutput<Self::Lattice>,
    ) {
        todo!()
    }
}
