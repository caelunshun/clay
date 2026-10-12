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

trait Fifo {
    type Elem;

    fn len(&self) -> u32;

    fn push_front(&mut self, elem: Elem);

    fn pop_back(&mut self) -> Elem;
}

trait Debug {
    fn print(&self) {}
}

fn print_contents(s: @dyn Fifo<Elem: Debug>) {
    let s = s.use;

    let mut i = 0;

    while i < s.len() {
        let elem = s.pop_back();
        elem.print();
        s.push_front(elem);
        i += 1;
    }
}
