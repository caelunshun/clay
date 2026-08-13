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
pub enum PromiseSink<'tcx, T> {
    Probe(PromiseProbe),
    Report(PromiseReporter<'tcx, T>),
}

impl<T> From<PromiseProbe> for PromiseSink<'_, T> {
    fn from(probe: PromiseProbe) -> Self {
        PromiseSink::Probe(probe)
    }
}

impl<'tcx, T> From<PromiseReporter<'tcx, T>> for PromiseSink<'tcx, T> {
    fn from(reporter: PromiseReporter<'tcx, T>) -> Self {
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

pub struct PromiseReporter<'tcx, T> {
    created_at: &'static Location<'static>,
    handler: Box<dyn 'tcx + Fn(&mut ClauseCx<'tcx>, T) -> ErrorGuaranteed>,
}

impl<T> fmt::Debug for PromiseReporter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PromiseReporter @ {}", self.created_at)
    }
}

impl<'tcx, T> PromiseReporter<'tcx, T> {
    #[track_caller]
    pub fn new(f: impl 'tcx + FnOnce(&mut ClauseCx<'tcx>, T) -> ErrorGuaranteed) -> Self {
        let f = Cell::new(Some(f));

        Self {
            created_at: Location::caller(),
            handler: Box::new(move |ccx, error| {
                f.take().expect("reporter called more than once")(ccx, error)
            }),
        }
    }

    pub fn report(&self, ccx: &mut ClauseCx<'tcx>, error: T) -> ErrorGuaranteed {
        (self.handler)(ccx, error)
    }
}

pub trait ReportableError<'tcx>: Sized {
    fn report(self, ccx: &mut ClauseCx<'tcx>) -> ErrorGuaranteed;
}

// === Promise === //

#[must_use]
pub struct Promise<'tcx, T: 'tcx> {
    builder: Rc<dyn 'tcx + PromiseNodeBuilder<'tcx, Error = T>>,
}

impl<'tcx, T: 'tcx> Promise<'tcx, T> {
    pub fn new_root() -> (Self, PromiseHandle<'tcx, T>) {
        let promise = Rc::new(PromiseNodeOrigin::default());

        let builder = Promise {
            builder: promise.clone(),
        };
        let handle = PromiseHandle { promise };

        (builder, handle)
    }

    pub fn new_join(
        sources: impl IntoIterator<Item = Promise<'tcx, T>>,
    ) -> Promise<'tcx, Vec<Option<T>>> {
        let sources = sources.into_iter().collect::<Vec<_>>();

        let trivially_accepted = sources
            .iter()
            .filter(|v| v.builder.already_accepted_during_build())
            .count();

        let promise = Rc::new(PromiseNodeJoiner {
            target: LateBoundPromiseNodeTarget::default(),
            err_resolutions: Cell::new((0..sources.len()).map(|_| None::<T>).collect::<Vec<_>>()),
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

    pub fn map<V>(self, f: impl 'tcx + FnOnce(&mut ClauseCx<'tcx>, T) -> V) -> Promise<'tcx, V>
    where
        T: 'tcx,
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

    pub fn remediator(self, f: impl 'tcx + FnOnce(&mut ClauseCx<'tcx>, &mut T)) -> Self {
        self.map(move |ccx, mut error| {
            f(ccx, &mut error);
            error
        })
    }

    pub fn sink(self, sink: impl Into<PromiseSink<'tcx, T>>) {
        self.builder.set_target(BoundPromiseNodeTarget::new(
            Rc::new(PromiseNodeSink { sink: sink.into() }),
            0,
        ));
    }

    pub fn sink_auto_report(self)
    where
        T: ReportableError<'tcx>,
    {
        self.sink(PromiseReporter::new(|ccx, err: T| err.report(ccx)));
    }
}

// === PromiseHandle === //

pub struct PromiseHandle<'tcx, T: 'tcx> {
    promise: Rc<PromiseNodeOrigin<'tcx, T>>,
}

impl<'tcx, T: 'tcx> PromiseHandle<'tcx, T> {
    pub fn accept(self, ccx: &mut ClauseCx<'tcx>, mode: PromiseMode) {
        match mode {
            PromiseMode::RootContext => self.promise.target.get().accept_on_root(ccx),
            PromiseMode::ProbeContext => {
                // (probes don't care)
            }
        }
    }

    pub fn reject(self, ccx: &mut ClauseCx<'tcx>, mode: PromiseMode, error: T) {
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
struct LateBoundPromiseNodeTarget<'tcx, T> {
    target: OnceCell<BoundPromiseNodeTarget<'tcx, T>>,
}

impl<'tcx, T> LateBoundPromiseNodeTarget<'tcx, T> {
    fn bind(&self, target: BoundPromiseNodeTarget<'tcx, T>) {
        self.target.set(target).ok().expect("bound more than once")
    }

    fn get(&self) -> &BoundPromiseNodeTarget<'tcx, T> {
        self.target.get().expect("incomplete promise")
    }
}

struct BoundPromiseNodeTarget<'tcx, T> {
    receiver: Rc<dyn 'tcx + PromiseNodeTarget<'tcx, Error = T>>,
    userdata: u32,
}

impl<'tcx, T> BoundPromiseNodeTarget<'tcx, T> {
    pub fn new(receiver: Rc<dyn 'tcx + PromiseNodeTarget<'tcx, Error = T>>, userdata: u32) -> Self {
        Self { receiver, userdata }
    }

    pub fn accept_on_root(&self, ccx: &mut ClauseCx<'tcx>) {
        self.receiver.accept_on_root(ccx, self.userdata);
    }

    pub fn reject_on_root(&self, ccx: &mut ClauseCx<'tcx>, error: T) {
        self.receiver.reject_on_root(ccx, error, self.userdata);
    }

    pub fn reject_on_fork(&self) {
        self.receiver.reject_on_fork();
    }
}

// === Promise Nodes === //

#[derive_where(Default)]
struct PromiseNodeOrigin<'tcx, T> {
    target: LateBoundPromiseNodeTarget<'tcx, T>,
    probe_rejected_somewhere: Cell<bool>,
}

impl<'tcx, T> PromiseNodeBuilder<'tcx> for PromiseNodeOrigin<'tcx, T> {
    type Error = T;

    fn set_target(&self, target: BoundPromiseNodeTarget<'tcx, Self::Error>) {
        self.target.bind(target);
    }

    fn already_accepted_during_build(&self) -> bool {
        false
    }
}

struct PromiseNodeJoiner<'tcx, T> {
    target: LateBoundPromiseNodeTarget<'tcx, Vec<Option<T>>>,
    err_resolutions: Cell<Vec<Option<T>>>,
    all_resolutions_remaining: Cell<u32>,
    poisoned_with_err: Cell<bool>,
}

impl<'tcx, T> PromiseNodeBuilder<'tcx> for PromiseNodeJoiner<'tcx, T> {
    type Error = Vec<Option<T>>;

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

impl<'tcx, T> PromiseNodeTarget<'tcx> for PromiseNodeJoiner<'tcx, T> {
    type Error = T;

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

impl<'tcx, T> PromiseNodeJoiner<'tcx, T> {
    fn resolve_child(&self, ccx: &mut ClauseCx<'tcx>, idx: u32, resolution: Option<T>) {
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

struct PromiseNodeMapper<'tcx, T, V, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, T) -> V,
{
    _ty: PhantomData<fn(T) -> T>,
    target: LateBoundPromiseNodeTarget<'tcx, V>,
    mapper: Cell<Option<F>>,
    already_accepted_during_build: bool,
}

impl<'tcx, T, V, F> PromiseNodeBuilder<'tcx> for PromiseNodeMapper<'tcx, T, V, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, T) -> V,
{
    type Error = V;

    fn set_target(&self, target: BoundPromiseNodeTarget<'tcx, Self::Error>) {
        self.target.bind(target);
    }

    fn already_accepted_during_build(&self) -> bool {
        self.already_accepted_during_build
    }
}

impl<'tcx, T, V, F> PromiseNodeTarget<'tcx> for PromiseNodeMapper<'tcx, T, V, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, T) -> V,
{
    type Error = T;

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

struct PromiseNodeSink<'tcx, T> {
    sink: PromiseSink<'tcx, T>,
}

impl<'tcx, T> PromiseNodeTarget<'tcx> for PromiseNodeSink<'tcx, T> {
    type Error = T;

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
