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
        ccx: &mut ClauseCx<'tcx>,
        sources: impl IntoIterator<Item = Promise<'tcx, T>>,
    ) -> Promise<'tcx, Vec<Option<T>>> {
        let sources = sources.into_iter().collect::<Vec<_>>();

        let promise = Rc::new(PromiseNodeJoiner {
            target: PromiseNodeBindSlot::default(),
            err_resolutions: Cell::new((0..sources.len()).map(|_| None::<T>).collect::<Vec<_>>()),
            all_resolutions_remaining: Cell::new(sources.len() as u32),
            poisoned_with_err: Cell::new(false),
        });

        for (idx, source) in sources.iter().enumerate() {
            source.builder.bind_target(
                ccx,
                BoundPromiseNodeTarget::new(promise.clone(), idx as u32),
            );
        }

        Promise { builder: promise }
    }

    pub fn map<V>(
        self,
        ccx: &mut ClauseCx<'tcx>,
        f: impl 'tcx + FnOnce(&mut ClauseCx<'tcx>, T) -> V,
    ) -> Promise<'tcx, V>
    where
        T: 'tcx,
    {
        let promise = Rc::new(PromiseNodeMapper {
            _ty: PhantomData,
            target: PromiseNodeBindSlot::default(),
            mapper: Cell::new(Some(f)),
        });

        self.builder
            .bind_target(ccx, BoundPromiseNodeTarget::new(promise.clone(), 0));

        Promise { builder: promise }
    }

    pub fn remediator(
        self,
        ccx: &mut ClauseCx<'tcx>,
        f: impl 'tcx + FnOnce(&mut ClauseCx<'tcx>, &mut T),
    ) -> Self {
        self.map(ccx, move |ccx, mut error| {
            f(ccx, &mut error);
            error
        })
    }

    pub fn sink(self, ccx: &mut ClauseCx<'tcx>, sink: impl Into<PromiseSink<'tcx, T>>) {
        self.builder.bind_target(
            ccx,
            BoundPromiseNodeTarget::new(Rc::new(PromiseNodeSink { sink: sink.into() }), 0),
        );
    }

    pub fn sink_auto_report(self, ccx: &mut ClauseCx<'tcx>)
    where
        T: ReportableError<'tcx>,
    {
        self.sink(ccx, PromiseReporter::new(|ccx, err: T| err.report(ccx)));
    }
}

// === PromiseHandle === //

pub struct PromiseHandle<'tcx, T: 'tcx> {
    promise: Rc<PromiseNodeOrigin<'tcx, T>>,
}

impl<'tcx, T: 'tcx> PromiseHandle<'tcx, T> {
    pub fn accept(self, ccx: &mut ClauseCx<'tcx>, mode: PromiseMode) {
        match mode {
            PromiseMode::RootContext => self.promise.target.accept_once_for_report(ccx),
            PromiseMode::ProbeContext => {
                // (probes don't care)
            }
        }
    }

    pub fn reject(self, ccx: &mut ClauseCx<'tcx>, mode: PromiseMode, error: T) {
        match mode {
            PromiseMode::RootContext => self.promise.target.reject_once_for_report(ccx, error),
            PromiseMode::ProbeContext => {
                self.promise.target.reject_probe_sink();
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

    fn bind_target(
        &self,
        ccx: &mut ClauseCx<'tcx>,
        target: BoundPromiseNodeTarget<'tcx, Self::Error>,
    );
}

trait PromiseNodeTarget<'tcx> {
    type Error: Sized;

    fn accept_once_for_report(&self, ccx: &mut ClauseCx<'tcx>, userdata: u32);

    fn reject_once_for_report(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, userdata: u32);

    fn reject_probe_sink(&self, userdata: u32);
}

struct BoundPromiseNodeTarget<'tcx, T> {
    receiver: Rc<dyn 'tcx + PromiseNodeTarget<'tcx, Error = T>>,
    userdata: u32,
}

impl<'tcx, T> BoundPromiseNodeTarget<'tcx, T> {
    pub fn new(receiver: Rc<dyn 'tcx + PromiseNodeTarget<'tcx, Error = T>>, userdata: u32) -> Self {
        Self { receiver, userdata }
    }

    pub fn accept_once_for_report(&self, ccx: &mut ClauseCx<'tcx>) {
        self.receiver.accept_once_for_report(ccx, self.userdata);
    }

    pub fn reject_once_for_report(&self, ccx: &mut ClauseCx<'tcx>, error: T) {
        self.receiver
            .reject_once_for_report(ccx, error, self.userdata);
    }

    pub fn reject_probe_sink(&self) {
        self.receiver.reject_probe_sink(self.userdata);
    }
}

// === Promise Node Bind Slot === //

struct PromiseNodeBindSlot<'tcx, T> {
    target: OnceCell<BoundPromiseNodeTarget<'tcx, T>>,
    state: Cell<PromiseBindSlotState<T>>,
    rejected_if_probe: Cell<RejectedIfProbeState>,
}

enum PromiseBindSlotState<T> {
    Meaningless,
    UnboundAndUnsignalled,
    BoundWaitingResolution,
    ResolveReportAcceptedWaitingBinding,
    ResolveReportRejectedWaitingBinding(T),
    BoundAndSignalled,
}

#[derive(Copy, Clone)]
enum RejectedIfProbeState {
    NotRejected,
    RejectedWhileAwaitingBind,
    RejectedAfterBound,
}

impl<T> Default for PromiseNodeBindSlot<'_, T> {
    fn default() -> Self {
        Self {
            target: OnceCell::new(),
            state: Cell::new(PromiseBindSlotState::UnboundAndUnsignalled),
            rejected_if_probe: Cell::new(RejectedIfProbeState::NotRejected),
        }
    }
}

impl<'tcx, T> PromiseNodeBindSlot<'tcx, T> {
    fn bind_target(&self, ccx: &mut ClauseCx<'tcx>, target: BoundPromiseNodeTarget<'tcx, T>) {
        use PromiseBindSlotState::*;
        use RejectedIfProbeState::*;

        self.target.set(target).ok().expect("bound more than once");

        match self.state.replace(Meaningless) {
            Meaningless | BoundWaitingResolution { .. } | BoundAndSignalled { .. } => {
                unreachable!()
            }
            UnboundAndUnsignalled => {
                self.state.set(BoundWaitingResolution);
            }
            ResolveReportAcceptedWaitingBinding => {
                self.state.set(BoundAndSignalled);

                self.target.get().unwrap().accept_once_for_report(ccx);
            }
            ResolveReportRejectedWaitingBinding(error) => {
                self.state.set(BoundAndSignalled);

                self.target
                    .get()
                    .unwrap()
                    .reject_once_for_report(ccx, error);
            }
        }

        match self.rejected_if_probe.get() {
            NotRejected | RejectedAfterBound => {
                // (no-op)
            }
            RejectedWhileAwaitingBind => {
                self.target.get().unwrap().reject_probe_sink();
            }
        }
    }

    fn accept_once_for_report(&self, ccx: &mut ClauseCx<'tcx>) {
        use PromiseBindSlotState::*;

        match self.state.replace(Meaningless) {
            Meaningless => unreachable!(),
            UnboundAndUnsignalled => {
                self.state.set(ResolveReportAcceptedWaitingBinding);
            }
            BoundWaitingResolution => {
                self.target.get().unwrap().accept_once_for_report(ccx);

                self.state.set(BoundAndSignalled);
            }

            replaced @ (ResolveReportAcceptedWaitingBinding
            | ResolveReportRejectedWaitingBinding(_)
            | BoundAndSignalled) => {
                self.state.set(replaced);

                panic!("promise resolved more than once");
            }
        }
    }

    fn reject_once_for_report(&self, ccx: &mut ClauseCx<'tcx>, error: T) {
        use PromiseBindSlotState::*;

        match self.state.replace(Meaningless) {
            Meaningless => unreachable!(),

            UnboundAndUnsignalled => {
                self.state.set(ResolveReportRejectedWaitingBinding(error));
            }

            BoundWaitingResolution => {
                self.target
                    .get()
                    .unwrap()
                    .reject_once_for_report(ccx, error);

                self.state.set(BoundAndSignalled);
            }

            replaced @ (ResolveReportAcceptedWaitingBinding
            | ResolveReportRejectedWaitingBinding(_)
            | BoundAndSignalled) => {
                self.state.set(replaced);

                panic!("promise resolved more than once");
            }
        }
    }

    fn reject_probe_sink(&self) {
        use RejectedIfProbeState::*;

        match self.rejected_if_probe.get() {
            NotRejected => {
                // (fallthrough)
            }
            RejectedWhileAwaitingBind | RejectedAfterBound => return,
        }

        match self.target.get() {
            Some(target) => {
                target.reject_probe_sink();

                self.rejected_if_probe.set(RejectedAfterBound);
            }
            None => {
                self.rejected_if_probe.set(RejectedWhileAwaitingBind);
            }
        }
    }
}

// === Promise Nodes === //

#[derive_where(Default)]
struct PromiseNodeOrigin<'tcx, T> {
    target: PromiseNodeBindSlot<'tcx, T>,
}

impl<'tcx, T> PromiseNodeBuilder<'tcx> for PromiseNodeOrigin<'tcx, T> {
    type Error = T;

    fn bind_target(
        &self,
        ccx: &mut ClauseCx<'tcx>,
        target: BoundPromiseNodeTarget<'tcx, Self::Error>,
    ) {
        self.target.bind_target(ccx, target);
    }
}

struct PromiseNodeJoiner<'tcx, T> {
    target: PromiseNodeBindSlot<'tcx, Vec<Option<T>>>,
    err_resolutions: Cell<Vec<Option<T>>>,
    all_resolutions_remaining: Cell<u32>,
    poisoned_with_err: Cell<bool>,
}

impl<'tcx, T> PromiseNodeBuilder<'tcx> for PromiseNodeJoiner<'tcx, T> {
    type Error = Vec<Option<T>>;

    fn bind_target(
        &self,
        ccx: &mut ClauseCx<'tcx>,
        target: BoundPromiseNodeTarget<'tcx, Self::Error>,
    ) {
        self.target.bind_target(ccx, target);
    }
}

impl<'tcx, T> PromiseNodeTarget<'tcx> for PromiseNodeJoiner<'tcx, T> {
    type Error = T;

    fn accept_once_for_report(&self, ccx: &mut ClauseCx<'tcx>, userdata: u32) {
        self.resolve_child(ccx, userdata, None);
    }

    fn reject_once_for_report(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, userdata: u32) {
        self.resolve_child(ccx, userdata, Some(error));
    }

    fn reject_probe_sink(&self, _userdata: u32) {
        self.target.reject_probe_sink();
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
            self.target.reject_once_for_report(ccx, resolutions);
        } else {
            self.target.accept_once_for_report(ccx);
        }
    }
}

struct PromiseNodeMapper<'tcx, T, V, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, T) -> V,
{
    _ty: PhantomData<fn(T) -> T>,
    target: PromiseNodeBindSlot<'tcx, V>,
    mapper: Cell<Option<F>>,
}

impl<'tcx, T, V, F> PromiseNodeBuilder<'tcx> for PromiseNodeMapper<'tcx, T, V, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, T) -> V,
{
    type Error = V;

    fn bind_target(
        &self,
        ccx: &mut ClauseCx<'tcx>,
        target: BoundPromiseNodeTarget<'tcx, Self::Error>,
    ) {
        self.target.bind_target(ccx, target);
    }
}

impl<'tcx, T, V, F> PromiseNodeTarget<'tcx> for PromiseNodeMapper<'tcx, T, V, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, T) -> V,
{
    type Error = T;

    fn accept_once_for_report(&self, ccx: &mut ClauseCx<'tcx>, _userdata: u32) {
        self.target.accept_once_for_report(ccx);
    }

    fn reject_once_for_report(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, _userdata: u32) {
        let error = self.mapper.take().unwrap()(ccx, error);

        self.target.reject_once_for_report(ccx, error);
    }

    fn reject_probe_sink(&self, _userdata: u32) {
        self.target.reject_probe_sink();
    }
}

struct PromiseNodeSink<'tcx, T> {
    sink: PromiseSink<'tcx, T>,
}

impl<'tcx, T> PromiseNodeTarget<'tcx> for PromiseNodeSink<'tcx, T> {
    type Error = T;

    fn accept_once_for_report(&self, _ccx: &mut ClauseCx<'tcx>, _userdata: u32) {
        // (no-op)
    }

    fn reject_once_for_report(&self, ccx: &mut ClauseCx<'tcx>, error: Self::Error, _userdata: u32) {
        match &self.sink {
            PromiseSink::Probe(probe) => probe.signal_error(),
            PromiseSink::Report(reporter) => {
                reporter.report(ccx, error);
            }
        }
    }

    fn reject_probe_sink(&self, _userdata: u32) {
        match &self.sink {
            PromiseSink::Probe(probe) => probe.signal_error(),
            PromiseSink::Report(_reporter) => {
                // (no-op)
            }
        }
    }
}
