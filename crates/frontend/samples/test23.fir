pub mod std {
    #[lang("deref_trait")]
    pub trait Deref {
        type Target;
    }

    impl<'a, T: &longer 'a> Deref for &'a T {
        type Target = T;
    }

    impl<'a, T: &longer 'a> Deref for &'a mut T {
        type Target = T;
    }
}

pub struct Vec<T> {
    
}

impl<T> Vec<T> {
    pub fn push(me: &mut Self) {

    }
}

fn main<'a>(mut v: &'a &'a &'a Vec<()>) {
    v.push;
}
