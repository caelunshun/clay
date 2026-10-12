type FunkyIdentity<T> = <(T,) as FunkyIdentityHelper>::Out;

trait FunkyIdentityHelper {
    type Out;
}

impl<T> FunkyIdentityHelper for (T,) {
    type Out = T;
}

trait Foo {}

impl Foo for FunkyIdentity<i32> {}

impl Foo for FunkyIdentity<u32> {}

struct Wf<T: Foo>;

// FIXME: multiple applicable impls
struct Check(Wf<i32>);
