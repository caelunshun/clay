use crate::{base::ErrorGuaranteed, semantic::infer::ClauseCx};
use derive_where::derive_where;
use std::{
    cell::{Cell, OnceCell},
    fmt,
    marker::PhantomData,
    panic::Location,
    rc::Rc,
};

// === PromiseSink === //

#[derive_where(Debug)]
pub enum PromiseSink<'tcx, E> {
    Probe(PromiseProbe),
    Report(PromiseReporter<'tcx, E>),
}

impl<E> From<PromiseProbe> for PromiseSink<'_, E> {
    fn from(probe: PromiseProbe) -> Self {
        PromiseSink::Probe(probe)
    }
}

impl<'tcx, E> From<PromiseReporter<'tcx, E>> for PromiseSink<'tcx, E> {
    fn from(reporter: PromiseReporter<'tcx, E>) -> Self {
        PromiseSink::Report(reporter)
    }
}

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

pub struct PromiseReporter<'tcx, E> {
    created_at: &'static Location<'static>,
    handler: Box<dyn 'tcx + Fn(&mut ClauseCx<'tcx>, E) -> ErrorGuaranteed>,
}

impl<E> fmt::Debug for PromiseReporter<'_, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PromiseReporter @ {}", self.created_at)
    }
}

impl<'tcx, E> PromiseReporter<'tcx, E> {
    #[track_caller]
    pub fn new(f: impl 'tcx + FnOnce(&mut ClauseCx<'tcx>, E) -> ErrorGuaranteed) -> Self {
        let f = Cell::new(Some(f));

        Self {
            created_at: Location::caller(),
            handler: Box::new(move |ccx, error| {
                f.take().expect("reporter called more than once")(ccx, error)
            }),
        }
    }

    pub fn report(&self, ccx: &mut ClauseCx<'tcx>, error: E) -> ErrorGuaranteed {
        (self.handler)(ccx, error)
    }
}

pub trait ReportableError<'tcx>: Sized {
    fn report(self, ccx: &mut ClauseCx<'tcx>) -> ErrorGuaranteed;
}

// === Promise === //

#[must_use]
pub struct Promise<'tcx, E: 'tcx> {
    builder: Rc<dyn 'tcx + PromiseNodeBuilder<'tcx, Error = E>>,
}

impl<'tcx, E: 'tcx> Promise<'tcx, E> {
    pub fn new_root() -> (Self, PromiseHandle<'tcx, E>) {
        let promise = Rc::new(PromiseNodeOrigin::default());

        let builder = Promise {
            builder: promise.clone(),
        };
        let handle = PromiseHandle { promise };

        (builder, handle)
    }

    pub fn new_join(
        sources: impl IntoIterator<Item = Promise<'tcx, E>>,
    ) -> Promise<'tcx, Vec<Option<E>>> {
        let sources = sources.into_iter().collect::<Vec<_>>();

        let trivially_accepted = sources
            .iter()
            .filter(|v| v.builder.already_accepted_during_build())
            .count();

        let promise = Rc::new(PromiseNodeJoiner {
            target: LateBoundPromiseNodeTarget::default(),
            err_resolutions: Cell::new((0..sources.len()).map(|_| None::<E>).collect::<Vec<_>>()),
            all_resolutions_remaining: Cell::new((sources.len() - trivially_accepted) as u32),
            poisoned_with_err: Cell::new(false),
        });

        for (idx, source) in sources.iter().enumerate() {
            source
                .builder
                .set_target(BoundPromiseNodeTarget::new(promise.clone(), idx as u32));
        }

        Promise { builder: promise }
    }

    pub fn map<E2>(self, f: impl 'tcx + FnOnce(&mut ClauseCx<'tcx>, E) -> E2) -> Promise<'tcx, E2>
    where
        E: 'tcx,
    {
        let promise = Rc::new(PromiseNodeMapper {
            _ty: PhantomData,
            target: LateBoundPromiseNodeTarget::default(),
            mapper: Cell::new(Some(f)),
            already_accepted_during_build: self.builder.already_accepted_during_build(),
        });

        self.builder
            .set_target(BoundPromiseNodeTarget::new(promise.clone(), 0));

        Promise { builder: promise }
    }

    pub fn remediate(self, f: impl 'tcx + FnOnce(&mut ClauseCx<'tcx>, &mut E)) -> Self {
        self.map(move |ccx, mut error| {
            f(ccx, &mut error);
            error
        })
    }

    pub fn join(self, builder: &mut MultiPromiseBuilder<'tcx, E>) {
        builder.push(self);
    }

    pub fn sink(self, sink: impl Into<PromiseSink<'tcx, E>>) {
        self.builder.set_target(BoundPromiseNodeTarget::new(
            Rc::new(PromiseNodeSink { sink: sink.into() }),
            0,
        ));
    }

    pub fn sink_auto_report(self)
    where
        E: ReportableError<'tcx>,
    {
        self.sink(PromiseReporter::new(|ccx, err: E| err.report(ccx)));
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

    pub fn map<V>(self, f: impl FnOnce(T) -> V) -> PromiseValue<'tcx, V, E> {
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

    pub fn map_err<E2>(
        self,
        f: impl 'tcx + FnOnce(&mut ClauseCx<'tcx>, E) -> E2,
    ) -> PromiseValue<'tcx, T, E2> {
        self.map_promise(|p| p.map(f))
    }

    pub fn remediate(self, f: impl 'tcx + FnOnce(&mut ClauseCx<'tcx>, &mut E)) -> Self {
        self.map_promise(|p| p.remediate(f))
    }

    pub fn join(self, builder: &mut MultiPromiseBuilder<'tcx, E>) -> T {
        self.finish_promise(|p| p.join(builder))
    }

    pub fn sink(self, sink: impl Into<PromiseSink<'tcx, E>>) -> T {
        self.finish_promise(|p| p.sink(sink))
    }

    pub fn sink_auto_report(self) -> T
    where
        E: ReportableError<'tcx>,
    {
        self.finish_promise(|p| p.sink_auto_report())
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

// === PromiseHandle === //

pub struct PromiseHandle<'tcx, E: 'tcx> {
    promise: Rc<PromiseNodeOrigin<'tcx, E>>,
}

impl<'tcx, E: 'tcx> PromiseHandle<'tcx, E> {
    pub fn accept(self, ccx: &mut ClauseCx<'tcx>, mode: PromiseMode) {
        match mode {
            PromiseMode::RootContext => self.promise.target.get().accept_on_root(ccx),
            PromiseMode::ProbeContext => {
                // (probes don't care)
            }
        }
    }

    pub fn reject(self, ccx: &mut ClauseCx<'tcx>, mode: PromiseMode, error: E) {
        match mode {
            PromiseMode::RootContext => self.promise.target.get().reject_on_root(ccx, error),
            PromiseMode::ProbeContext => {
                if self.promise.probe_rejected_somewhere.replace(true) {
                    // (already saturated as rejected)
                    return;
                }

                self.promise.target.get().reject_on_fork();
            }
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
    pub fn should_resolve(self) -> bool {
        matches!(self, Self::RootContext)
    }
}

// === Promise Node Traits === //

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

// === Promise Nodes === //

#[derive_where(Default)]
struct PromiseNodeOrigin<'tcx, E> {
    target: LateBoundPromiseNodeTarget<'tcx, E>,
    probe_rejected_somewhere: Cell<bool>,
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

struct PromiseNodeJoiner<'tcx, E> {
    target: LateBoundPromiseNodeTarget<'tcx, Vec<Option<E>>>,
    err_resolutions: Cell<Vec<Option<E>>>,
    all_resolutions_remaining: Cell<u32>,
    poisoned_with_err: Cell<bool>,
}

impl<'tcx, E> PromiseNodeBuilder<'tcx> for PromiseNodeJoiner<'tcx, E> {
    type Error = Vec<Option<E>>;

    fn set_target(&self, target: BoundPromiseNodeTarget<'tcx, Self::Error>) {
        self.target.bind(target);
    }

    fn already_accepted_during_build(&self) -> bool {
        let err_resolutions = self.err_resolutions.take();
        let already_accepted = err_resolutions.is_empty();
        self.err_resolutions.set(err_resolutions);
        already_accepted
    }
}

impl<'tcx, E> PromiseNodeTarget<'tcx> for PromiseNodeJoiner<'tcx, E> {
    type Error = E;

    fn accept_on_root(&self, ccx: &mut ClauseCx<'tcx>, userdata: u32) {
        self.resolve_child(ccx, userdata, None);
    }

    fn reject_on_root(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, userdata: u32) {
        self.resolve_child(ccx, userdata, Some(error));
    }

    fn reject_on_fork(&self) {
        self.target.get().reject_on_fork();
    }
}

impl<'tcx, E> PromiseNodeJoiner<'tcx, E> {
    fn resolve_child(&self, ccx: &mut ClauseCx<'tcx>, idx: u32, resolution: Option<E>) {
        if resolution.is_some() {
            self.poisoned_with_err.set(true);
        }

        let mut resolutions = self.err_resolutions.take();
        resolutions[idx as usize] = resolution;

        self.all_resolutions_remaining.update(|v| v - 1);

        if self.all_resolutions_remaining.get() > 0 {
            self.err_resolutions.set(resolutions);
            return;
        }

        if self.poisoned_with_err.get() {
            self.target.get().reject_on_root(ccx, resolutions);
        } else {
            self.target.get().accept_on_root(ccx);
        }
    }
}

struct PromiseNodeMapper<'tcx, E1, E2, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, E1) -> E2,
{
    _ty: PhantomData<fn(E1) -> E1>,
    target: LateBoundPromiseNodeTarget<'tcx, E2>,
    mapper: Cell<Option<F>>,
    already_accepted_during_build: bool,
}

impl<'tcx, E1, E2, F> PromiseNodeBuilder<'tcx> for PromiseNodeMapper<'tcx, E1, E2, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, E1) -> E2,
{
    type Error = E2;

    fn set_target(&self, target: BoundPromiseNodeTarget<'tcx, Self::Error>) {
        self.target.bind(target);
    }

    fn already_accepted_during_build(&self) -> bool {
        self.already_accepted_during_build
    }
}

impl<'tcx, E1, E2, F> PromiseNodeTarget<'tcx> for PromiseNodeMapper<'tcx, E1, E2, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, E1) -> E2,
{
    type Error = E1;

    fn accept_on_root(&self, ccx: &mut ClauseCx<'tcx>, _userdata: u32) {
        self.target.get().accept_on_root(ccx);
    }

    fn reject_on_root(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, _userdata: u32) {
        let error = self.mapper.take().unwrap()(ccx, error);

        self.target.get().reject_on_root(ccx, error);
    }

    fn reject_on_fork(&self) {
        self.target.get().reject_on_fork();
    }
}

struct PromiseNodeSink<'tcx, E> {
    sink: PromiseSink<'tcx, E>,
}

impl<'tcx, E> PromiseNodeTarget<'tcx> for PromiseNodeSink<'tcx, E> {
    type Error = E;

    fn accept_on_root(&self, _ccx: &mut ClauseCx<'tcx>, _userdata: u32) {
        // (no-op)
    }

    fn reject_on_root(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, _userdata: u32) {
        match &self.sink {
            PromiseSink::Probe(probe) => probe.signal_error(),
            PromiseSink::Report(reporter) => {
                reporter.report(ccx, error);
            }
        }
    }

    fn reject_on_fork(&self) {
        match &self.sink {
            PromiseSink::Probe(probe) => probe.signal_error(),
            PromiseSink::Report(_reporter) => {
                // (no-op)
            }
        }
    }
}
