pub struct Counter {
    count: @mut u32,
}

impl Counter {
    fn new() -> Self {
        let (self, self) = (self, self);

        /*Self {
            count: 0.gc,
        }*/
    }

    fn count(&self) -> u32 => *self.count;

    fn increment(&self) {
        self.count += 1;
    }

    fn gc(@self) {}
}

fn main() {
    let cnt = Counter::new();
    cnt.count();
}
