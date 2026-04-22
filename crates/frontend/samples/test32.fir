trait Projector {
    type Out;
}

trait Helper<T> {}

// We need to defer importing of HRTB `SigProject` and `SigAlias` types until the
// `HrtbSubstitutionFolder` is used.
fn uh_oh(v: @dyn for<T: Projector> Helper<<T as Projector>::Out>) {}
