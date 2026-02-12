use core::fmt;
use std::hash;

pub trait Handle: 'static + fmt::Debug + Copy + hash::Hash + Eq {}

impl<T: 'static + fmt::Debug + Copy + hash::Hash + Eq> Handle for T {}
