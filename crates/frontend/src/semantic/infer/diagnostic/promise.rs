use crate::{
    base::{Diag, ErrorGuaranteed},
    semantic::infer::{ClauseCx, ClausePrettyFmtOpts, ToDebugTree},
};
use bytemuck::{TransparentWrapper, TransparentWrapperAlloc as _};
use derive_where::derive_where;
use std::{
    cell::{Cell, OnceCell},
    fmt,
    marker::PhantomData,
    mem,
    rc::Rc,
};

// === Promise === //

#[derive(Debug, Clone, Default)]
pub struct PromiseProbe {
    had_error: Rc<Cell<bool>>,
}

impl PromiseProbe {
    pub fn signal_error(&self) {
        self.had_error.set(true);
    }

    pub fn had_error(&self) -> bool {
        self.had_error.get()
    }
}

pub type MultiPromise<'sess, E> = Promise<'sess, Vec<E>>;

#[must_use]
pub struct Promise<'sess, E: 'sess> {
    builder: Rc<dyn 'sess + PromiseNodeBuilder<'sess, Error = E>>,
}

impl<'sess, E: 'sess> Promise<'sess, E> {
    pub fn new() -> (Self, PromiseHandle<'sess, E>) {
        let node = Rc::new(PromiseNodeOrigin::default());

        let promise = Promise {
            builder: node.clone(),
        };
        let handle = PromiseHandle { promise: node };

        (promise, handle)
    }

    pub fn trivial() -> Self {
        Promise {
            builder: Rc::new(PromiseNodeTrivial::default()),
        }
    }

    pub fn filter_map<E2, F>(self, f: F) -> Promise<'sess, E2>
    where
        E2: 'sess,
        F: 'sess + FnOnce(&mut ClauseCx<'sess>, E) -> Result<E2, ErrorGuaranteed>,
    {
        let node = Rc::new(PromiseNodeFilterMapper::<E, E2, F> {
            _ty: PhantomData,
            target: LateBoundPromiseNodeTarget::default(),
            mapper: Cell::new(Some(f)),
            already_accepted_during_build: self.builder.already_accepted_during_build(),
        });

        self.builder
            .set_target(BoundPromiseNodeTarget::new(node.clone(), 0));

        Promise { builder: node }
    }

    // TODO: Use proper reporting machinery
    pub fn filter_delay_bug<E2, F>(self, f: F) -> Promise<'sess, E2>
    where
        E: fmt::Debug,
        E2: 'sess,
        F: 'sess + FnOnce(&mut ClauseCx<'sess>, E) -> Result<E2, E>,
    {
        self.filter_map(move |ccx, err| match f(ccx, err) {
            Ok(mapped) => Ok(mapped),
            Err(orig) => Err(Diag::anon_err(format_args!("{orig:#?}"))
                .to_delay_bug()
                .emit()),
        })
    }

    pub fn map<E2, F>(self, f: F) -> Promise<'sess, E2>
    where
        E2: 'sess,
        F: 'sess + FnOnce(&mut ClauseCx<'sess>, E) -> E2,
    {
        self.filter_map(move |ccx, err| Ok(f(ccx, err)))
    }

    pub fn remediate<F>(self, f: F) -> Self
    where
        F: 'sess + FnOnce(&mut ClauseCx<'sess>, &mut E),
    {
        self.map(move |ccx, mut error| {
            f(ccx, &mut error);
            error
        })
    }

    pub fn join(self, builder: &mut impl JoinablePromise<'sess, E>) {
        builder.push(self);
    }

    pub fn report_with<F>(self, f: F)
    where
        F: 'sess + FnOnce(&mut ClauseCx<'sess>, E) -> ErrorGuaranteed,
    {
        self.builder.set_target(BoundPromiseNodeTarget::new(
            Rc::new(PromiseNodeReportSink::<E, F> {
                _ty: PhantomData,
                reporter: Cell::new(Some(f)),
            }),
            0,
        ));
    }

    // TODO: Use proper reporting machinery
    pub fn report_loud(self)
    where
        E: ToDebugTree,
    {
        self.report_with(|ccx, err| {
            Diag::anon_err(format!(
                "\n{}",
                err.to_debug_tree(&ccx.pretty(ClausePrettyFmtOpts { verbose: true }))
            ))
            .emit()
        });
    }

    // TODO: Use proper reporting machinery
    pub fn report_delay_bug(self)
    where
        E: ToDebugTree,
    {
        self.report_with(|ccx, err| {
            Diag::anon_err(format!(
                "\n{}",
                err.to_debug_tree(&ccx.pretty(ClausePrettyFmtOpts { verbose: true }))
            ))
            .to_delay_bug()
            .emit()
        });
    }

    // TODO: Use bug machinery
    pub fn report_never(self) {
        self.report_with(|_ccx, _err| unreachable!());
    }

    pub fn probe(self, probe: PromiseProbe) {
        self.builder.set_target(BoundPromiseNodeTarget::new(
            Rc::new(PromiseNodeProbeSink::<E> {
                _ty: PhantomData,
                probe,
            }),
            0,
        ));
    }

    pub fn forward(self, ccx: &mut ClauseCx<'sess>, handle: PromiseHandle<'sess, E>) {
        if self.builder.already_accepted_during_build() {
            handle.accept(ccx);
            return;
        }

        self.builder.set_target(BoundPromiseNodeTarget::new(
            Rc::new(PromiseNodeForwardSink::<'sess, E> { handle }),
            0,
        ));
    }

    pub fn and_value<T>(self, value: T) -> PromiseValue<'sess, T, E> {
        PromiseValue::new(value, self)
    }
}

impl<'sess, E: 'sess> MultiPromise<'sess, E> {
    pub fn flat_join(self, builder: &mut MultiPromiseBuilder<'sess, E>) {
        builder.push_flat(self);
    }
}

pub type MultiPromiseValue<'sess, T, E> = PromiseValue<'sess, T, Vec<E>>;

#[must_use]
pub struct PromiseValue<'sess, T, E: 'sess> {
    pub value: T,
    pub promise: Promise<'sess, E>,
}

impl<'sess, T, E: 'sess> PromiseValue<'sess, T, E> {
    pub fn new(value: T, promise: Promise<'sess, E>) -> Self {
        Self { value, promise }
    }

    pub fn trivial(value: T) -> Self {
        Self {
            value,
            promise: Promise::trivial(),
        }
    }

    pub fn map_value<V>(self, f: impl FnOnce(T) -> V) -> PromiseValue<'sess, V, E> {
        PromiseValue {
            value: f(self.value),
            promise: self.promise,
        }
    }

    pub fn map_promise<E2: 'sess>(
        self,
        f: impl FnOnce(Promise<'sess, E>) -> Promise<'sess, E2>,
    ) -> PromiseValue<'sess, T, E2> {
        PromiseValue {
            value: self.value,
            promise: f(self.promise),
        }
    }

    pub fn finish_promise(self, f: impl FnOnce(Promise<'sess, E>)) -> T {
        f(self.promise);
        self.value
    }

    // Forwards
    pub fn filter_map<E2, F>(self, f: F) -> PromiseValue<'sess, T, E2>
    where
        E2: 'sess,
        F: 'sess + FnOnce(&mut ClauseCx<'sess>, E) -> Result<E2, ErrorGuaranteed>,
    {
        self.map_promise(|p| p.filter_map(f))
    }

    pub fn filter_delay_bug<E2, F>(self, f: F) -> PromiseValue<'sess, T, E2>
    where
        E: fmt::Debug,
        E2: 'sess,
        F: 'sess + FnOnce(&mut ClauseCx<'sess>, E) -> Result<E2, E>,
    {
        self.map_promise(|p| p.filter_delay_bug(f))
    }

    pub fn map<E2, F>(self, f: F) -> PromiseValue<'sess, T, E2>
    where
        E2: 'sess,
        F: 'sess + FnOnce(&mut ClauseCx<'sess>, E) -> E2,
    {
        self.map_promise(|p| p.map(f))
    }

    pub fn remediate<F>(self, f: F) -> Self
    where
        F: 'sess + FnOnce(&mut ClauseCx<'sess>, &mut E),
    {
        self.map_promise(|p| p.remediate(f))
    }

    pub fn join(self, builder: &mut impl JoinablePromise<'sess, E>) -> T {
        self.finish_promise(|p| p.join(builder))
    }

    pub fn report_with<F>(self, f: F) -> T
    where
        F: 'sess + FnOnce(&mut ClauseCx<'sess>, E) -> ErrorGuaranteed,
    {
        self.finish_promise(|p| p.report_with(f))
    }

    pub fn report_loud(self) -> T
    where
        E: ToDebugTree,
    {
        self.finish_promise(|p| p.report_loud())
    }

    pub fn report_delay_bug(self) -> T
    where
        E: ToDebugTree,
    {
        self.finish_promise(|p| p.report_delay_bug())
    }

    pub fn report_never(self) -> T {
        self.finish_promise(|p| p.report_never())
    }

    pub fn probe(self, probe: PromiseProbe) -> T {
        self.finish_promise(|p| p.probe(probe))
    }

    pub fn forward(self, ccx: &mut ClauseCx<'sess>, handle: PromiseHandle<'sess, E>) -> T {
        self.finish_promise(|p| p.forward(ccx, handle))
    }
}

impl<'sess, T, E: 'sess> MultiPromiseValue<'sess, T, E> {
    pub fn flat_join(self, builder: &mut MultiPromiseBuilder<'sess, E>) -> T {
        self.finish_promise(|p| p.flat_join(builder))
    }
}

// === PromiseHandle === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum PromiseMode {
    /// The context resolves promises and produces diagnostics when a promise is accepted or
    /// rejected. This is done only for the canonical context used for analysis.
    RootContext,

    /// The context never resolves promises and, instead, only notifies probes of errors when a
    /// promise is accepted or rejected. This is done only for all fork contexts used for probing an
    /// action.
    ProbeContext,
}

impl PromiseMode {
    pub fn is_root(self) -> bool {
        matches!(self, Self::RootContext)
    }
}

#[derive_where(Clone)]
pub struct PromiseHandle<'sess, E: 'sess> {
    promise: Rc<PromiseNodeOrigin<'sess, E>>,
}

impl<'sess, E: 'sess> fmt::Debug for PromiseHandle<'sess, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PromiseHandle").finish_non_exhaustive()
    }
}

impl<'sess, E: 'sess> PromiseHandle<'sess, E> {
    pub fn accept(&self, ccx: &mut ClauseCx<'sess>) {
        match ccx.promise_mode() {
            PromiseMode::RootContext => self.promise.accept_on_root(ccx),
            PromiseMode::ProbeContext => {
                // (probes don't care)
            }
        }
    }

    pub fn reject(&self, ccx: &mut ClauseCx<'sess>, error: E) {
        match ccx.promise_mode() {
            PromiseMode::RootContext => self.promise.reject_on_root(ccx, error),
            PromiseMode::ProbeContext => self.promise.reject_on_fork(),
        }
    }

    pub fn accept_if_not_rejected(&self, ccx: &mut ClauseCx<'sess>) {
        match ccx.promise_mode() {
            PromiseMode::RootContext => {
                if !self.promise.already_report_resolved.get() {
                    self.promise.accept_on_root(ccx);
                }
            }
            PromiseMode::ProbeContext => {
                // (accept has no effect here)
            }
        }
    }
}

pub trait AnyPromiseHandle<'sess> {
    fn accept(&self, ccx: &mut ClauseCx<'sess>);
}

impl<'sess, E: 'sess> AnyPromiseHandle<'sess> for PromiseHandle<'sess, E> {
    fn accept(&self, ccx: &mut ClauseCx<'sess>) {
        self.accept(ccx);
    }
}

// === Promise Joiners === //

pub trait JoinablePromise<'sess, E: 'sess>: Sized {
    fn push(&mut self, promise: Promise<'sess, E>);

    fn push_handle(&mut self) -> PromiseHandle<'sess, E> {
        let (promise, handle) = Promise::new();
        self.push(promise);
        handle
    }

    fn with(mut self, promise: Promise<'sess, E>) -> Self {
        self.push(promise);
        self
    }

    fn extend(&mut self, promises: impl IntoIterator<Item = Promise<'sess, E>>) {
        for promise in promises {
            self.push(promise);
        }
    }

    fn with_many(mut self, promises: impl IntoIterator<Item = Promise<'sess, E>>) -> Self {
        self.extend(promises);
        self
    }
}

pub struct RawMultiPromiseBuilder<'sess, A: 'sess> {
    node: Rc<PromiseNodeJoiner<'sess, A>>,
}

impl<'sess, A: 'sess> Default for RawMultiPromiseBuilder<'sess, A> {
    fn default() -> Self {
        let node = Rc::new(PromiseNodeJoiner {
            target: LateBoundPromiseNodeTarget::default(),
            // Initialized during `finish`.
            err_resolutions: Cell::new(None),
            all_resolutions_remaining: Cell::new(0),
            poisoned_with_err: Cell::new(false),
        });

        Self { node }
    }
}

impl<'sess, A: 'sess> RawMultiPromiseBuilder<'sess, A> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push<E, F>(&mut self, target: Promise<'sess, E>, userdata: u32, initializer: F)
    where
        E: 'sess,
        F: 'static + Copy + Fn(&mut A, E, u32),
    {
        if !target.builder.already_accepted_during_build() {
            self.node.all_resolutions_remaining.update(|v| v + 1);
        }

        target.builder.set_target(BoundPromiseNodeTarget::new(
            self.node.clone().target(initializer),
            userdata,
        ));
    }

    pub fn with<E, F>(mut self, target: Promise<'sess, E>, userdata: u32, initializer: F) -> Self
    where
        E: 'sess,
        F: 'static + Copy + Fn(&mut A, E, u32),
    {
        self.push(target, userdata, initializer);
        self
    }

    pub fn finish(self, err_resolutions: A) -> Promise<'sess, A> {
        self.node.err_resolutions.set(Some(err_resolutions));

        Promise { builder: self.node }
    }
}

#[derive_where(Default)]
pub struct MultiPromiseBuilder<'sess, E: 'sess> {
    builder: RawMultiPromiseBuilder<'sess, Vec<E>>,
}

impl<'sess, E: 'sess> MultiPromiseBuilder<'sess, E> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push_flat(&mut self, promise: MultiPromise<'sess, E>) {
        self.builder.push(promise, 0, |aggregate, errors, _idx| {
            aggregate.extend(errors);
        });
    }

    pub fn finish(self) -> MultiPromise<'sess, E> {
        self.builder.finish(Vec::new())
    }
}

impl<'sess, E: 'sess> JoinablePromise<'sess, E> for MultiPromiseBuilder<'sess, E> {
    fn push(&mut self, promise: Promise<'sess, E>) {
        self.builder.push(promise, 0, |aggregate, error, _idx| {
            aggregate.push(error);
        });
    }
}

#[derive_where(Default)]
pub struct FixedMultiPromiseBuilder<'sess, E: 'sess> {
    builder: RawMultiPromiseBuilder<'sess, Vec<Option<E>>>,
    len: u32,
}

impl<'sess, E: 'sess> FixedMultiPromiseBuilder<'sess, E> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn finish(self) -> Promise<'sess, Vec<Option<E>>> {
        self.builder.finish((0..self.len).map(|_| None).collect())
    }
}

impl<'sess, E: 'sess> JoinablePromise<'sess, E> for FixedMultiPromiseBuilder<'sess, E> {
    fn push(&mut self, promise: Promise<'sess, E>) {
        let idx = self.len;
        self.len += 1;

        self.builder.push(promise, idx, |aggregate, error, idx| {
            aggregate[idx as usize] = Some(error);
        });
    }
}

#[doc(hidden)]
pub mod typed_joiner_internals {
    use super::RawMultiPromiseBuilder;
    pub use std::option::Option;

    pub fn new_raw_builder_with_hint<'sess, A: 'sess>(
        _f: fn() -> A,
    ) -> RawMultiPromiseBuilder<'sess, A> {
        RawMultiPromiseBuilder::new()
    }
}

#[macro_export]
macro_rules! typed_joiner {
    (
        $( let $dep_name:ident = $dep:expr; )*
        |$ccx:ident|
        $($body:tt)*
    ) => {{
        #[allow(non_camel_case_types)]
        struct ErrAggregate<$($dep_name),*> {
            $($dep_name: $crate::semantic::infer::typed_joiner_internals::Option<$dep_name>,)*
        }

        $crate::semantic::infer::typed_joiner_internals::new_raw_builder_with_hint(|| ErrAggregate {
                $($dep_name: $crate::semantic::infer::typed_joiner_internals::Option::None,)*
            })
            $(.with($dep, 0u32, |aggregate, value, _idx| {
                aggregate.$dep_name = $crate::semantic::infer::typed_joiner_internals::Option::Some(
                    value
                );
            }))*
            .finish(ErrAggregate {
                $($dep_name: $crate::semantic::infer::typed_joiner_internals::Option::None,)*
            })
            .map(#[allow(unused)] move |$ccx, ErrAggregate { $($dep_name),* }| {
                $($body)*
            })
    }};
}

// === Promise Nodes === //

trait PromiseNodeBuilder<'sess> {
    type Error: Sized;

    fn set_target(&self, target: BoundPromiseNodeTarget<'sess, Self::Error>);

    fn already_accepted_during_build(&self) -> bool;
}

trait PromiseNodeTarget<'sess> {
    type Error: Sized;

    /// Resolves the promise and its downstream promises as accepted, potentially producing a
    /// report. This method assumes the promise has been connected to a sink. This method can only
    /// be called once.
    fn accept_on_root(&self, ccx: &mut ClauseCx<'sess>, userdata: u32);

    /// Resolves the promise and its downstream promises as rejected, potentially producing a
    /// report. This method assumes the promise has been connected to a sink. This method can only
    /// be called once.
    fn reject_on_root(&self, ccx: &mut ClauseCx<'sess>, error: Self::Error, userdata: u32);

    /// Resolves the promise and its downstream promises as rejected if the sink is sink is a probe.
    /// This method can (well, technically, should) only be called once.
    fn reject_on_fork(&self);
}

#[derive_where(Default)]
struct LateBoundPromiseNodeTarget<'sess, E> {
    target: OnceCell<BoundPromiseNodeTarget<'sess, E>>,
}

impl<'sess, E> LateBoundPromiseNodeTarget<'sess, E> {
    fn bind(&self, target: BoundPromiseNodeTarget<'sess, E>) {
        self.target.set(target).ok().expect("bound more than once")
    }

    fn get(&self) -> &BoundPromiseNodeTarget<'sess, E> {
        self.target.get().expect("incomplete promise")
    }
}

struct BoundPromiseNodeTarget<'sess, E> {
    receiver: Rc<dyn 'sess + PromiseNodeTarget<'sess, Error = E>>,
    userdata: u32,
}

impl<'sess, E> BoundPromiseNodeTarget<'sess, E> {
    pub fn new(
        receiver: Rc<dyn 'sess + PromiseNodeTarget<'sess, Error = E>>,
        userdata: u32,
    ) -> Self {
        Self { receiver, userdata }
    }

    pub fn accept_on_root(&self, ccx: &mut ClauseCx<'sess>) {
        self.receiver.accept_on_root(ccx, self.userdata);
    }

    pub fn reject_on_root(&self, ccx: &mut ClauseCx<'sess>, error: E) {
        self.receiver.reject_on_root(ccx, error, self.userdata);
    }

    pub fn reject_on_fork(&self) {
        self.receiver.reject_on_fork();
    }
}

#[derive_where(Default)]
struct PromiseNodeOrigin<'sess, E> {
    target: LateBoundPromiseNodeTarget<'sess, E>,
    already_report_resolved: Cell<bool>,
    already_probe_resolved: Cell<bool>,
}

impl<'sess, E> PromiseNodeBuilder<'sess> for PromiseNodeOrigin<'sess, E> {
    type Error = E;

    fn set_target(&self, target: BoundPromiseNodeTarget<'sess, Self::Error>) {
        self.target.bind(target);
    }

    fn already_accepted_during_build(&self) -> bool {
        false
    }
}

impl<'sess, E> PromiseNodeOrigin<'sess, E> {
    fn accept_on_root(&self, ccx: &mut ClauseCx<'sess>) {
        assert!(
            !self.already_report_resolved.replace(true),
            "cannot report-resolve promise more than once"
        );

        self.target.get().accept_on_root(ccx)
    }

    fn reject_on_root(&self, ccx: &mut ClauseCx<'sess>, error: E) {
        assert!(
            !self.already_report_resolved.replace(true),
            "cannot report-resolve promise more than once"
        );

        self.target.get().reject_on_root(ccx, error)
    }

    fn reject_on_fork(&self) {
        if self.already_probe_resolved.replace(true) {
            return;
        }

        self.target.get().reject_on_fork();
    }
}

#[derive_where(Default)]
struct PromiseNodeTrivial<'sess, E> {
    _ty: PhantomData<fn(&'sess (), E) -> (&'sess (), E)>,
}

impl<'sess, E> PromiseNodeBuilder<'sess> for PromiseNodeTrivial<'sess, E> {
    type Error = E;

    fn set_target(&self, _target: BoundPromiseNodeTarget<'sess, Self::Error>) {
        // (no-op)
    }

    fn already_accepted_during_build(&self) -> bool {
        true
    }
}

struct PromiseNodeJoiner<'sess, A> {
    target: LateBoundPromiseNodeTarget<'sess, A>,
    err_resolutions: Cell<Option<A>>,
    all_resolutions_remaining: Cell<u32>,
    poisoned_with_err: Cell<bool>,
}

impl<'sess, A> PromiseNodeBuilder<'sess> for PromiseNodeJoiner<'sess, A> {
    type Error = A;

    fn set_target(&self, target: BoundPromiseNodeTarget<'sess, Self::Error>) {
        self.target.bind(target);
    }

    fn already_accepted_during_build(&self) -> bool {
        self.all_resolutions_remaining.get() == 0
    }
}

impl<'sess, A> PromiseNodeJoiner<'sess, A> {
    fn target<E, F>(
        self: Rc<Self>,
        initializer: F,
    ) -> Rc<dyn 'sess + PromiseNodeTarget<'sess, Error = E>>
    where
        A: 'sess,
        E: 'sess,
        F: 'static + Copy + Fn(&mut A, E, u32),
    {
        #[derive(TransparentWrapper)]
        #[repr(transparent)]
        #[transparent(PromiseNodeJoiner<'sess, A>)]
        struct NodeTarget<'sess, A, E, F> {
            _ty: PhantomData<fn(E, F) -> (E, F)>,
            inner: PromiseNodeJoiner<'sess, A>,
        }

        impl<'sess, A, E, F> PromiseNodeTarget<'sess> for NodeTarget<'sess, A, E, F>
        where
            F: 'static + Copy + Fn(&mut A, E, u32),
        {
            type Error = E;

            fn accept_on_root(&self, ccx: &mut ClauseCx<'sess>, userdata: u32) {
                self.resolve_child(ccx, userdata, None);
            }

            fn reject_on_root(&self, ccx: &mut ClauseCx<'sess>, error: Self::Error, userdata: u32) {
                self.resolve_child(ccx, userdata, Some(error));
            }

            fn reject_on_fork(&self) {
                self.inner.target.get().reject_on_fork();
            }
        }

        impl<'sess, A, E, F> NodeTarget<'sess, A, E, F>
        where
            F: 'static + Copy + Fn(&mut A, E, u32),
        {
            fn resolve_child(&self, ccx: &mut ClauseCx<'sess>, idx: u32, resolution: Option<E>) {
                if resolution.is_some() {
                    self.inner.poisoned_with_err.set(true);
                }

                let mut resolutions = self.inner.err_resolutions.take().unwrap();

                let initializer = unsafe {
                    // `mem::conjure_zst` at home
                    #[allow(clippy::uninit_assumed_init)]
                    mem::MaybeUninit::<F>::uninit().assume_init()
                };

                if let Some(resolution) = resolution {
                    initializer(&mut resolutions, resolution, idx);
                }

                self.inner.all_resolutions_remaining.update(|v| v - 1);

                if self.inner.all_resolutions_remaining.get() > 0 {
                    self.inner.err_resolutions.set(Some(resolutions));
                    return;
                }

                if self.inner.poisoned_with_err.get() {
                    self.inner.target.get().reject_on_root(ccx, resolutions);
                } else {
                    self.inner.target.get().accept_on_root(ccx);
                }
            }
        }

        const {
            assert!(mem::size_of::<F>() == 0, "`initializer` must be a ZST");
        }

        // `initializer` served its purpose of acting as a proof of safe inhabitance of `F`.
        _ = initializer;

        NodeTarget::<A, E, F>::wrap_rc(self)
    }
}

struct PromiseNodeFilterMapper<'sess, E1, E2, F>
where
    F: FnOnce(&mut ClauseCx<'sess>, E1) -> Result<E2, ErrorGuaranteed>,
{
    _ty: PhantomData<fn(E1) -> E1>,
    target: LateBoundPromiseNodeTarget<'sess, E2>,
    mapper: Cell<Option<F>>,
    already_accepted_during_build: bool,
}

impl<'sess, E1, E2, F> PromiseNodeBuilder<'sess> for PromiseNodeFilterMapper<'sess, E1, E2, F>
where
    F: FnOnce(&mut ClauseCx<'sess>, E1) -> Result<E2, ErrorGuaranteed>,
{
    type Error = E2;

    fn set_target(&self, target: BoundPromiseNodeTarget<'sess, Self::Error>) {
        self.target.bind(target);
    }

    fn already_accepted_during_build(&self) -> bool {
        self.already_accepted_during_build
    }
}

impl<'sess, E1, E2, F> PromiseNodeTarget<'sess> for PromiseNodeFilterMapper<'sess, E1, E2, F>
where
    F: FnOnce(&mut ClauseCx<'sess>, E1) -> Result<E2, ErrorGuaranteed>,
{
    type Error = E1;

    fn accept_on_root(&self, ccx: &mut ClauseCx<'sess>, _userdata: u32) {
        self.target.get().accept_on_root(ccx);
    }

    fn reject_on_root(&self, ccx: &mut ClauseCx<'sess>, error: Self::Error, _userdata: u32) {
        match self.mapper.take().unwrap()(ccx, error) {
            Ok(error) => self.target.get().reject_on_root(ccx, error),
            Err(ErrorGuaranteed) => self.target.get().accept_on_root(ccx),
        }
    }

    fn reject_on_fork(&self) {
        self.target.get().reject_on_fork();
    }
}

struct PromiseNodeReportSink<'sess, E, F>
where
    F: FnOnce(&mut ClauseCx<'sess>, E) -> ErrorGuaranteed,
{
    _ty: PhantomData<fn(&'sess (), E) -> (&'sess (), E)>,
    reporter: Cell<Option<F>>,
}

impl<'sess, E, F> PromiseNodeTarget<'sess> for PromiseNodeReportSink<'sess, E, F>
where
    F: FnOnce(&mut ClauseCx<'sess>, E) -> ErrorGuaranteed,
{
    type Error = E;

    fn accept_on_root(&self, _ccx: &mut ClauseCx<'sess>, _userdata: u32) {
        // (no-op)
    }

    fn reject_on_root(&self, ccx: &mut ClauseCx<'sess>, error: Self::Error, _userdata: u32) {
        self.reporter.take().expect("already rejected")(ccx, error);
    }

    fn reject_on_fork(&self) {
        // (no-op)
    }
}

struct PromiseNodeProbeSink<E> {
    _ty: PhantomData<fn(E) -> E>,
    probe: PromiseProbe,
}

impl<'sess, E> PromiseNodeTarget<'sess> for PromiseNodeProbeSink<E> {
    type Error = E;

    fn accept_on_root(&self, _ccx: &mut ClauseCx<'sess>, _userdata: u32) {
        // (no-op)
    }

    fn reject_on_root(&self, _ccx: &mut ClauseCx<'sess>, _error: Self::Error, _userdata: u32) {
        // (no-op)
    }

    fn reject_on_fork(&self) {
        self.probe.signal_error();
    }
}

struct PromiseNodeForwardSink<'sess, E> {
    handle: PromiseHandle<'sess, E>,
}

impl<'sess, E> PromiseNodeTarget<'sess> for PromiseNodeForwardSink<'sess, E> {
    type Error = E;

    fn accept_on_root(&self, ccx: &mut ClauseCx<'sess>, _userdata: u32) {
        self.handle.promise.accept_on_root(ccx);
    }

    fn reject_on_root(&self, ccx: &mut ClauseCx<'sess>, error: Self::Error, _userdata: u32) {
        self.handle.promise.reject_on_root(ccx, error);
    }

    fn reject_on_fork(&self) {
        self.handle.promise.reject_on_fork();
    }
}
