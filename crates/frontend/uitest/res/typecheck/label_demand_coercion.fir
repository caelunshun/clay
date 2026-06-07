#[lang("deref_trait")]
trait Deref {
    type Target;
}

impl<'a, T: &longer 'a> Deref for &'a T {
    type Target = T;
}

impl<'a, T: &longer 'a> Deref for &'a mut T {
    type Target = T;
}

fn main() {
    let foo = 'a: {
        if true {
            break 'a &();
        }

        if true {
            break 'a &mut ();
        }
    };
}
