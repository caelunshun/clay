#[lang("fn_once_trait")]
pub trait FnOnce<I, O> {}

mod types {
    use super::FnOnce;

    fn hrtb_types<T>(v: T) {}

    fn taker_types<F: for<T> FnOnce<(T,), ()>>(f: F) {}

    fn demo_types() {
        // Accepted.
        taker_types(hrtb_types);

        // Rejected.
        taker_types(hrtb_types::<_>);
    }

}

mod regions {
    use super::FnOnce;

    fn hrtb_regions<'a>(v: &'a ()) {}

    fn taker_regions<F: for<'a> FnOnce<(&'a (),), ()>>(f: F) {}

    fn demo_types() {
        // Accepted.
        taker_regions(hrtb_regions);

        // FIXME: Should be rejected.
        taker_regions(hrtb_regions::<'_>);
    }
}
