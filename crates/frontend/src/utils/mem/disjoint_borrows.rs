use std::marker::PhantomData;

#[derive(Default)]
pub struct DisjointBorrowsScratch {
    borrowed_cells: Vec<BorrowState>,
    undo_set: Vec<usize>,
}

#[derive(Copy, Clone)]
enum BorrowState {
    None,
    Mut,
    Ref,
}

impl DisjointBorrowsScratch {
    pub fn builder<'s, 'a, T>(
        &'s mut self,
        target: &'a mut [T],
    ) -> DisjointBorrowsBuilder<'s, 'a, T> {
        for idx in self.undo_set.drain(..) {
            self.borrowed_cells[idx] = BorrowState::None;
        }

        if self.borrowed_cells.len() < target.len() {
            self.borrowed_cells.resize(target.len(), BorrowState::None);
        }

        DisjointBorrowsBuilder {
            _ty: PhantomData,
            scratch: self,
            target,
        }
    }
}

pub struct DisjointBorrowsBuilder<'s, 'a, T> {
    _ty: PhantomData<&'a mut [T]>,
    scratch: &'s mut DisjointBorrowsScratch,
    target: *mut [T],
}

impl<'s, 'a, T> DisjointBorrowsBuilder<'s, 'a, T> {
    pub fn get(&mut self, index: usize) -> &'a T {
        assert!(index < self.target.len());

        let state = &mut self.scratch.borrowed_cells[index];

        match state {
            BorrowState::None | BorrowState::Ref => {
                *state = BorrowState::Ref;
            }
            BorrowState::Mut => {
                panic!("invalid immutable borrow");
            }
        }

        self.scratch.undo_set.push(index);

        unsafe { &*self.target.cast::<T>().add(index) }
    }

    pub fn get_mut(&mut self, index: usize) -> &'a mut T {
        assert!(index < self.target.len());

        let state = &mut self.scratch.borrowed_cells[index];

        match state {
            BorrowState::None => {
                *state = BorrowState::Mut;
            }
            BorrowState::Mut | BorrowState::Ref => {
                panic!("invalid mutable borrow");
            }
        }

        self.scratch.undo_set.push(index);

        unsafe { &mut *self.target.cast::<T>().add(index) }
    }
}
