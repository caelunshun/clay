pub trait LendingIterator {
    type Iter: for<'a: &shorter Self> LendingOutput<'a>;
}

pub trait LendingOutput<'a> {
    // Very weird lifetime. Should usually be `&longer 'a`.
    type Output: &shorter 'a;
}

pub struct LendingOutputSimpleMut<T>;

impl<'a, T: &longer 'a> LendingOutput<'a> for LendingOutputSimpleMut<T> {
    // Valid because `'a == 'a`.
    type Output = &'a mut T;
}

pub fn next<
    'a,
    L: LendingIterator + &longer 'a,
>(
    iter: &'a mut L,
) -> <<L as LendingIterator>::Iter as LendingOutput<'a>>::Output {
    todo()
}

pub fn demo() {
    // Local is given the inference lifetime `'local0`.
    let mut iter: MyLendingIterator;

    // Case 1: `type Output: &shorter 'a;`
    //
    // Local is given the inference lifetime `'local1`.
    //
    // `'a` is instantiated as the inference variable `'inf_a` and we get the constraint
    // `'local0 outlives 'inf_a`.
    //
    // Returned type has LUB universal `'lub0` with permission `'inf_a can outlive 'lub0` derived
    // from the `&shorter 'inf_a` clause. In other words, it can live for any duration so long as
    // `'inf_a` outlives that.
    //
    // The local's value must outlive its lifetime so we get the region outlives constraint
    // `'lub0 outlives 'local1`.
    //
    // We should find the constraint `'local0 outlives 'local1` and, indeed we do...
    //
    // `'local0 outlives 'inf_a outlives 'lub0 outlives 'local1`.
    //
    // Case 2: `type Output: &longer 'a;`
    //
    // Local is given the inference lifetime `'local1`.
    //
    // `'a` is instantiated as the inference variable `'inf_a` and we get the constraint
    // `'local0 outlives 'inf_a`.
    //
    // Returned type has LUB universal `'lub0` with permission `'lub0 can outlive 'inf_a` derived
    // from the `&longer 'inf_a` clause. In other words, it can live for any duration so long as
    // that outlives `'inf_a`.
    //
    // The local's value must outlive its lifetime so we get the region outlives constraint
    // `'lub0 outlives 'local1`.
    //
    // We should find the constraint `'local0 outlives 'local1` but we don't...
    //
    // `'local0 outlives 'inf_a`
    // `lub0 can outlive 'inf_a`
    // `'lub0 outlives 'local1`
    //
    // TODO: What????????
    //
    // Case 3: `type Output;`
    //
    // TODO
    let elem = next(&mut iter);

    drop(iter);
    drop(elem);
}
