use crate::{
    base::{ErrorGuaranteed, HardDiag},
    semantic::infer::ClauseCx,
};
use bytemuck::{TransparentWrapper, TransparentWrapperAlloc as _};
use derive_where::derive_where;
use std::{
    cell::{Cell, OnceCell},
    marker::PhantomData,
    mem,
    rc::Rc,
};

// === Public API === //

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

pub trait ErrorToDiag<'tcx>: Sized {
    fn to_diag(self, ccx: &mut ClauseCx<'tcx>) -> HardDiag;
}

#[must_use]
pub struct Promise<'tcx, E: 'tcx> {
    builder: Rc<dyn 'tcx + PromiseNodeBuilder<'tcx, Error = E>>,
}

impl<'tcx, E: 'tcx> Promise<'tcx, E> {
    pub fn new_root() -> (Self, PromiseHandle<'tcx, E>) {
        let node = Rc::new(PromiseNodeOrigin::default());

        let promise = Promise {
            builder: node.clone(),
        };
        let handle = PromiseHandle { promise: node };

        (promise, handle)
    }

    pub fn new_join<I>(sources: I) -> Promise<'tcx, Vec<Option<E>>>
    where
        I: IntoIterator<Item = Promise<'tcx, E>>,
    {
        let sources = sources.into_iter().collect::<Vec<_>>();

        let trivially_accepted = sources
            .iter()
            .filter(|v| v.builder.already_accepted_during_build())
            .count();

        let node = Rc::new(PromiseNodeJoiner {
            target: LateBoundPromiseNodeTarget::default(),
            err_resolutions: Cell::new(Some(
                (0..sources.len()).map(|_| None::<E>).collect::<Vec<_>>(),
            )),
            all_resolutions_remaining: Cell::new((sources.len() - trivially_accepted) as u32),
            poisoned_with_err: Cell::new(false),
        });

        for (idx, source) in sources.iter().enumerate() {
            source.builder.set_target(BoundPromiseNodeTarget::new(
                node.clone().target(|error_list, error, idx| {
                    error_list[idx as usize] = Some(error);
                }),
                idx as u32,
            ));
        }

        Promise { builder: node }
    }

    pub fn filter_map<E2, F>(self, f: F) -> Promise<'tcx, E2>
    where
        E2: 'tcx,
        F: 'tcx + FnOnce(&mut ClauseCx<'tcx>, E) -> Result<E2, ErrorGuaranteed>,
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

    pub fn filter_delay_bug<E2, F>(self, f: F) -> Promise<'tcx, E2>
    where
        E: ErrorToDiag<'tcx>,
        E2: 'tcx,
        F: 'tcx + FnOnce(&mut ClauseCx<'tcx>, E) -> Result<E2, E>,
    {
        self.filter_map(move |ccx, err| match f(ccx, err) {
            Ok(mapped) => Ok(mapped),
            Err(orig) => Err(orig.to_diag(ccx).to_delay_bug().emit()),
        })
    }

    pub fn map<E2, F>(self, f: F) -> Promise<'tcx, E2>
    where
        E2: 'tcx,
        F: 'tcx + FnOnce(&mut ClauseCx<'tcx>, E) -> E2,
    {
        self.filter_map(move |ccx, err| Ok(f(ccx, err)))
    }

    pub fn remediate<F>(self, f: F) -> Self
    where
        F: 'tcx + FnOnce(&mut ClauseCx<'tcx>, &mut E),
    {
        self.map(move |ccx, mut error| {
            f(ccx, &mut error);
            error
        })
    }

    pub fn join(self, builder: &mut MultiPromiseBuilder<'tcx, E>) {
        builder.push(self);
    }

    pub fn report_with<F>(self, f: F)
    where
        F: 'tcx + FnOnce(&mut ClauseCx<'tcx>, E) -> ErrorGuaranteed,
    {
        self.builder.set_target(BoundPromiseNodeTarget::new(
            Rc::new(PromiseNodeReportSink::<E, F> {
                _ty: PhantomData,
                reporter: Cell::new(Some(f)),
            }),
            0,
        ));
    }

    pub fn report_loud(self)
    where
        E: ErrorToDiag<'tcx>,
    {
        self.report_with(|ccx, err| err.to_diag(ccx).emit());
    }

    pub fn report_delay_bug(self)
    where
        E: ErrorToDiag<'tcx>,
    {
        self.report_with(|ccx, err| err.to_diag(ccx).to_delay_bug().emit());
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

    pub fn forward(self, ccx: &mut ClauseCx<'tcx>, handle: PromiseHandle<'tcx, E>) {
        if self.builder.already_accepted_during_build() {
            handle.accept(ccx);
            return;
        }

        self.builder.set_target(BoundPromiseNodeTarget::new(
            Rc::new(PromiseNodeForwardSink::<'tcx, E> { handle }),
            0,
        ));
    }

    pub fn and_value<T>(self, value: T) -> PromiseValue<'tcx, T, E> {
        PromiseValue::new(value, self)
    }
}

#[must_use]
pub struct PromiseValue<'tcx, T, E: 'tcx> {
    pub value: T,
    pub promise: Promise<'tcx, E>,
}

impl<'tcx, T, E: 'tcx> PromiseValue<'tcx, T, E> {
    pub fn new(value: T, promise: Promise<'tcx, E>) -> Self {
        Self { value, promise }
    }

    pub fn map_value<V>(self, f: impl FnOnce(T) -> V) -> PromiseValue<'tcx, V, E> {
        PromiseValue {
            value: f(self.value),
            promise: self.promise,
        }
    }

    pub fn map_promise<E2: 'tcx>(
        self,
        f: impl FnOnce(Promise<'tcx, E>) -> Promise<'tcx, E2>,
    ) -> PromiseValue<'tcx, T, E2> {
        PromiseValue {
            value: self.value,
            promise: f(self.promise),
        }
    }

    pub fn finish_promise(self, f: impl FnOnce(Promise<'tcx, E>)) -> T {
        f(self.promise);
        self.value
    }

    // Forwards
    pub fn filter_map<E2, F>(self, f: F) -> PromiseValue<'tcx, T, E2>
    where
        E2: 'tcx,
        F: 'tcx + FnOnce(&mut ClauseCx<'tcx>, E) -> Result<E2, ErrorGuaranteed>,
    {
        self.map_promise(|p| p.filter_map(f))
    }

    pub fn filter_delay_bug<E2, F>(self, f: F) -> PromiseValue<'tcx, T, E2>
    where
        E: ErrorToDiag<'tcx>,
        E2: 'tcx,
        F: 'tcx + FnOnce(&mut ClauseCx<'tcx>, E) -> Result<E2, E>,
    {
        self.map_promise(|p| p.filter_delay_bug(f))
    }

    pub fn map<E2, F>(self, f: F) -> PromiseValue<'tcx, T, E2>
    where
        E2: 'tcx,
        F: 'tcx + FnOnce(&mut ClauseCx<'tcx>, E) -> E2,
    {
        self.map_promise(|p| p.map(f))
    }

    pub fn remediate<F>(self, f: F) -> Self
    where
        F: 'tcx + FnOnce(&mut ClauseCx<'tcx>, &mut E),
    {
        self.map_promise(|p| p.remediate(f))
    }

    pub fn join(self, builder: &mut MultiPromiseBuilder<'tcx, E>) -> T {
        self.finish_promise(|p| p.join(builder))
    }

    pub fn report_with<F>(self, f: F) -> T
    where
        F: 'tcx + FnOnce(&mut ClauseCx<'tcx>, E) -> ErrorGuaranteed,
    {
        self.finish_promise(|p| p.report_with(f))
    }

    pub fn report_loud(self) -> T
    where
        E: ErrorToDiag<'tcx>,
    {
        self.finish_promise(|p| p.report_loud())
    }

    pub fn report_delay_bug(self) -> T
    where
        E: ErrorToDiag<'tcx>,
    {
        self.finish_promise(|p| p.report_delay_bug())
    }

    pub fn probe(self, probe: PromiseProbe) -> T {
        self.finish_promise(|p| p.probe(probe))
    }

    pub fn forward(self, ccx: &mut ClauseCx<'tcx>, handle: PromiseHandle<'tcx, E>) -> T {
        self.finish_promise(|p| p.forward(ccx, handle))
    }
}

#[derive_where(Default)]
pub struct MultiPromiseBuilder<'tcx, E: 'tcx> {
    sources: Vec<Promise<'tcx, E>>,
}

impl<'tcx, E: 'tcx> MultiPromiseBuilder<'tcx, E> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, promise: Promise<'tcx, E>) {
        self.sources.push(promise)
    }

    pub fn with(mut self, promise: Promise<'tcx, E>) -> Self {
        self.push(promise);
        self
    }

    pub fn extend(&mut self, promises: impl IntoIterator<Item = Promise<'tcx, E>>) {
        self.sources.extend(promises);
    }

    pub fn with_many(mut self, promises: impl IntoIterator<Item = Promise<'tcx, E>>) -> Self {
        self.extend(promises);
        self
    }

    pub fn finish(self) -> Promise<'tcx, Vec<Option<E>>> {
        Promise::new_join(self.sources)
    }
}

#[derive_where(Clone)]
pub struct PromiseHandle<'tcx, E: 'tcx> {
    promise: Rc<PromiseNodeOrigin<'tcx, E>>,
}

impl<'tcx, E: 'tcx> PromiseHandle<'tcx, E> {
    pub fn accept(&self, ccx: &mut ClauseCx<'tcx>) {
        match ccx.promise_mode() {
            PromiseMode::RootContext => self.promise.accept_on_root(ccx),
            PromiseMode::ProbeContext => {
                // (probes don't care)
            }
        }
    }

    pub fn reject(&self, ccx: &mut ClauseCx<'tcx>, error: E) {
        match ccx.promise_mode() {
            PromiseMode::RootContext => self.promise.reject_on_root(ccx, error),
            PromiseMode::ProbeContext => self.promise.reject_on_fork(),
        }
    }
}

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

// === Promise Nodes === //

trait PromiseNodeBuilder<'tcx> {
    type Error: Sized;

    fn set_target(&self, target: BoundPromiseNodeTarget<'tcx, Self::Error>);

    fn already_accepted_during_build(&self) -> bool;
}

trait PromiseNodeTarget<'tcx> {
    type Error: Sized;

    /// Resolves the promise and its downstream promises as accepted, potentially producing a
    /// report. This method assumes the promise has been connected to a sink. This method can only
    /// be called once.
    fn accept_on_root(&self, ccx: &mut ClauseCx<'tcx>, userdata: u32);

    /// Resolves the promise and its downstream promises as rejected, potentially producing a
    /// report. This method assumes the promise has been connected to a sink. This method can only
    /// be called once.
    fn reject_on_root(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, userdata: u32);

    /// Resolves the promise and its downstream promises as rejected if the sink is sink is a probe.
    /// This method can (well, technically, should) only be called once.
    fn reject_on_fork(&self);
}

#[derive_where(Default)]
struct LateBoundPromiseNodeTarget<'tcx, E> {
    target: OnceCell<BoundPromiseNodeTarget<'tcx, E>>,
}

impl<'tcx, E> LateBoundPromiseNodeTarget<'tcx, E> {
    fn bind(&self, target: BoundPromiseNodeTarget<'tcx, E>) {
        self.target.set(target).ok().expect("bound more than once")
    }

    fn get(&self) -> &BoundPromiseNodeTarget<'tcx, E> {
        self.target.get().expect("incomplete promise")
    }
}

struct BoundPromiseNodeTarget<'tcx, E> {
    receiver: Rc<dyn 'tcx + PromiseNodeTarget<'tcx, Error = E>>,
    userdata: u32,
}

impl<'tcx, E> BoundPromiseNodeTarget<'tcx, E> {
    pub fn new(receiver: Rc<dyn 'tcx + PromiseNodeTarget<'tcx, Error = E>>, userdata: u32) -> Self {
        Self { receiver, userdata }
    }

    pub fn accept_on_root(&self, ccx: &mut ClauseCx<'tcx>) {
        self.receiver.accept_on_root(ccx, self.userdata);
    }

    pub fn reject_on_root(&self, ccx: &mut ClauseCx<'tcx>, error: E) {
        self.receiver.reject_on_root(ccx, error, self.userdata);
    }

    pub fn reject_on_fork(&self) {
        self.receiver.reject_on_fork();
    }
}

#[derive_where(Default)]
struct PromiseNodeOrigin<'tcx, E> {
    target: LateBoundPromiseNodeTarget<'tcx, E>,
    already_report_resolved: Cell<bool>,
    already_probe_resolved: Cell<bool>,
}

impl<'tcx, E> PromiseNodeBuilder<'tcx> for PromiseNodeOrigin<'tcx, E> {
    type Error = E;

    fn set_target(&self, target: BoundPromiseNodeTarget<'tcx, Self::Error>) {
        self.target.bind(target);
    }

    fn already_accepted_during_build(&self) -> bool {
        false
    }
}

impl<'tcx, E> PromiseNodeOrigin<'tcx, E> {
    fn accept_on_root(&self, ccx: &mut ClauseCx<'tcx>) {
        assert!(
            !self.already_report_resolved.replace(true),
            "cannot report-resolve promise more than once"
        );

        self.target.get().accept_on_root(ccx)
    }

    fn reject_on_root(&self, ccx: &mut ClauseCx<'tcx>, error: E) {
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

struct PromiseNodeJoiner<'tcx, A> {
    target: LateBoundPromiseNodeTarget<'tcx, A>,
    err_resolutions: Cell<Option<A>>,
    all_resolutions_remaining: Cell<u32>,
    poisoned_with_err: Cell<bool>,
}

impl<'tcx, A> PromiseNodeBuilder<'tcx> for PromiseNodeJoiner<'tcx, A> {
    type Error = A;

    fn set_target(&self, target: BoundPromiseNodeTarget<'tcx, Self::Error>) {
        self.target.bind(target);
    }

    fn already_accepted_during_build(&self) -> bool {
        self.all_resolutions_remaining.get() == 0
    }
}

impl<'tcx, A> PromiseNodeJoiner<'tcx, A> {
    fn target<E, F>(
        self: Rc<Self>,
        initializer: F,
    ) -> Rc<dyn 'tcx + PromiseNodeTarget<'tcx, Error = E>>
    where
        A: 'tcx,
        E: 'tcx,
        F: 'static + Copy + Fn(&mut A, E, u32),
    {
        #[derive(TransparentWrapper)]
        #[repr(transparent)]
        #[transparent(PromiseNodeJoiner<'tcx, A>)]
        struct NodeTarget<'tcx, A, E, F> {
            _ty: PhantomData<fn(E, F) -> (E, F)>,
            inner: PromiseNodeJoiner<'tcx, A>,
        }

        impl<'tcx, A, E, F> PromiseNodeTarget<'tcx> for NodeTarget<'tcx, A, E, F>
        where
            F: 'static + Copy + Fn(&mut A, E, u32),
        {
            type Error = E;

            fn accept_on_root(&self, ccx: &mut ClauseCx<'tcx>, userdata: u32) {
                self.resolve_child(ccx, userdata, None);
            }

            fn reject_on_root(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, userdata: u32) {
                self.resolve_child(ccx, userdata, Some(error));
            }

            fn reject_on_fork(&self) {
                self.inner.target.get().reject_on_fork();
            }
        }

        impl<'tcx, A, E, F> NodeTarget<'tcx, A, E, F>
        where
            F: 'static + Copy + Fn(&mut A, E, u32),
        {
            fn resolve_child(&self, ccx: &mut ClauseCx<'tcx>, idx: u32, resolution: Option<E>) {
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

struct PromiseNodeFilterMapper<'tcx, E1, E2, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, E1) -> Result<E2, ErrorGuaranteed>,
{
    _ty: PhantomData<fn(E1) -> E1>,
    target: LateBoundPromiseNodeTarget<'tcx, E2>,
    mapper: Cell<Option<F>>,
    already_accepted_during_build: bool,
}

impl<'tcx, E1, E2, F> PromiseNodeBuilder<'tcx> for PromiseNodeFilterMapper<'tcx, E1, E2, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, E1) -> Result<E2, ErrorGuaranteed>,
{
    type Error = E2;

    fn set_target(&self, target: BoundPromiseNodeTarget<'tcx, Self::Error>) {
        self.target.bind(target);
    }

    fn already_accepted_during_build(&self) -> bool {
        self.already_accepted_during_build
    }
}

impl<'tcx, E1, E2, F> PromiseNodeTarget<'tcx> for PromiseNodeFilterMapper<'tcx, E1, E2, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, E1) -> Result<E2, ErrorGuaranteed>,
{
    type Error = E1;

    fn accept_on_root(&self, ccx: &mut ClauseCx<'tcx>, _userdata: u32) {
        self.target.get().accept_on_root(ccx);
    }

    fn reject_on_root(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, _userdata: u32) {
        match self.mapper.take().unwrap()(ccx, error) {
            Ok(error) => self.target.get().reject_on_root(ccx, error),
            Err(ErrorGuaranteed) => self.target.get().accept_on_root(ccx),
        }
    }

    fn reject_on_fork(&self) {
        self.target.get().reject_on_fork();
    }
}

struct PromiseNodeReportSink<'tcx, E, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, E) -> ErrorGuaranteed,
{
    _ty: PhantomData<fn(&'tcx (), E) -> (&'tcx (), E)>,
    reporter: Cell<Option<F>>,
}

impl<'tcx, E, F> PromiseNodeTarget<'tcx> for PromiseNodeReportSink<'tcx, E, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, E) -> ErrorGuaranteed,
{
    type Error = E;

    fn accept_on_root(&self, _ccx: &mut ClauseCx<'tcx>, _userdata: u32) {
        // (no-op)
    }

    fn reject_on_root(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, _userdata: u32) {
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

impl<'tcx, E> PromiseNodeTarget<'tcx> for PromiseNodeProbeSink<E> {
    type Error = E;

    fn accept_on_root(&self, _ccx: &mut ClauseCx<'tcx>, _userdata: u32) {
        // (no-op)
    }

    fn reject_on_root(&self, _ccx: &mut ClauseCx<'tcx>, _error: Self::Error, _userdata: u32) {
        // (no-op)
    }

    fn reject_on_fork(&self) {
        self.probe.signal_error();
    }
}

struct PromiseNodeForwardSink<'tcx, E> {
    handle: PromiseHandle<'tcx, E>,
}

impl<'tcx, E> PromiseNodeTarget<'tcx> for PromiseNodeForwardSink<'tcx, E> {
    type Error = E;

    fn accept_on_root(&self, ccx: &mut ClauseCx<'tcx>, _userdata: u32) {
        self.handle.promise.accept_on_root(ccx);
    }

    fn reject_on_root(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, _userdata: u32) {
        self.handle.promise.reject_on_root(ccx, error);
    }

    fn reject_on_fork(&self) {
        self.handle.promise.reject_on_fork();
    }
}
