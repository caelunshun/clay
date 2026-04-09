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

    #[lang("fn_once_trait")]
    pub trait FnOnce<I, O> {}
}

fn main() {
    let always_live = 1;
    let sometimes_dead = 1;
    let ref_1 = &always_live;
    let ref_2 = &sometimes_dead;

    let ref_3 = meow(ref_1, ref_2);
    sometimes_dead;
    ref_3;
}

fn meow<'a>(a: &'a u32, b: &'a u32) -> &'a u32 {
    a
}

fn mewo<'a, 'b>(a: &'a u32, b: &'b u32) -> &'a u32 {
    a
}
