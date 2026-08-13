use crate::{base::ErrorGuaranteed, semantic::infer::ClauseCx};
use derive_where::derive_where;
use smallvec::SmallVec;
use std::{
    cell::{Cell, OnceCell},
    fmt,
    marker::PhantomData,
    panic::Location,
    rc::Rc,
};

// === PromiseMode === //

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

// === Promise Public Interface === //

#[must_use]
pub struct Promise<'tcx, T: 'tcx> {
    builder: Rc<dyn 'tcx + AnyPromiseBuilder<'tcx, Error = T>>,
}

impl<'tcx, T: 'tcx> Promise<'tcx, T> {
    pub fn new_root() -> (Self, PromiseHandle<'tcx, T>) {
        let promise = Rc::new(PromiseOrigin::default());

        let builder = Promise {
            builder: promise.clone(),
        };
        let handle = PromiseHandle { promise };

        (builder, handle)
    }

    pub fn new_join(
        ccx: &mut ClauseCx<'tcx>,
        targets: impl IntoIterator<Item = Promise<'tcx, T>>,
    ) -> Self {
        todo!()
    }

    pub fn map<V>(
        self,
        ccx: &mut ClauseCx<'tcx>,
        f: impl 'tcx + FnOnce(&mut ClauseCx<'tcx>, T) -> V,
    ) -> Promise<'tcx, V>
    where
        T: 'tcx,
    {
        let promise = Rc::new(PromiseMapper {
            _ty: PhantomData,
            target: PromiseBindSlot::default(),
            mapper: Cell::new(Some(f)),
        });

        self.builder
            .bind_target(ccx, BoundAnyPromiseTarget::new(promise.clone(), 0));

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
        todo!()
    }
}

pub struct PromiseHandle<'tcx, T: 'tcx> {
    promise: Rc<PromiseOrigin<'tcx, T>>,
}

// === Promise Traits === //

trait AnyPromiseBuilder<'tcx> {
    type Error: Sized;

    fn bind_target(
        &self,
        ccx: &mut ClauseCx<'tcx>,
        target: BoundAnyPromiseTarget<'tcx, Self::Error>,
    );
}

trait AnyPromiseTarget<'tcx> {
    type Error: Sized;

    fn accept_once_if_sink_is_report(&self, userdata: u32);

    fn reject_once_if_sink_is_report(
        &self,
        ccx: &mut ClauseCx<'tcx>,
        error: Self::Error,
        userdata: u32,
    );

    fn reject_if_sink_is_probe(&self, userdata: u32);
}

struct BoundAnyPromiseTarget<'tcx, T> {
    receiver: Rc<dyn 'tcx + AnyPromiseTarget<'tcx, Error = T>>,
    userdata: u32,
}

impl<'tcx, T> BoundAnyPromiseTarget<'tcx, T> {
    pub fn new(receiver: Rc<dyn 'tcx + AnyPromiseTarget<'tcx, Error = T>>, userdata: u32) -> Self {
        Self { receiver, userdata }
    }

    pub fn accept_once_if_sink_is_report(&self) {
        self.receiver.accept_once_if_sink_is_report(self.userdata);
    }

    pub fn reject_once_if_sink_is_report(&self, ccx: &mut ClauseCx<'tcx>, error: T) {
        self.receiver
            .reject_once_if_sink_is_report(ccx, error, self.userdata);
    }

    pub fn reject_if_sink_is_probe(&self) {
        self.receiver.reject_if_sink_is_probe(self.userdata);
    }
}

// === Promise Bind Slot === //

struct PromiseBindSlot<'tcx, T> {
    target: OnceCell<BoundAnyPromiseTarget<'tcx, T>>,
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

impl<T> Default for PromiseBindSlot<'_, T> {
    fn default() -> Self {
        Self {
            target: OnceCell::new(),
            state: Cell::new(PromiseBindSlotState::UnboundAndUnsignalled),
            rejected_if_probe: Cell::new(RejectedIfProbeState::NotRejected),
        }
    }
}

impl<'tcx, T> PromiseBindSlot<'tcx, T> {
    fn bind_target(&self, ccx: &mut ClauseCx<'tcx>, target: BoundAnyPromiseTarget<'tcx, T>) {
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

                self.target.get().unwrap().accept_once_if_sink_is_report();
            }
            ResolveReportRejectedWaitingBinding(error) => {
                self.state.set(BoundAndSignalled);

                self.target
                    .get()
                    .unwrap()
                    .reject_once_if_sink_is_report(ccx, error);
            }
        }

        match self.rejected_if_probe.get() {
            NotRejected | RejectedAfterBound => {
                // (no-op)
            }
            RejectedWhileAwaitingBind => {
                self.target.get().unwrap().reject_if_sink_is_probe();
            }
        }
    }

    fn accept_once_if_sink_is_report(&self) {
        use PromiseBindSlotState::*;

        match self.state.replace(Meaningless) {
            Meaningless => unreachable!(),
            UnboundAndUnsignalled => {
                self.state.set(ResolveReportAcceptedWaitingBinding);
            }
            BoundWaitingResolution => {
                self.target.get().unwrap().accept_once_if_sink_is_report();

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

    fn reject_once_if_sink_is_report(&self, ccx: &mut ClauseCx<'tcx>, error: T) {
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
                    .reject_once_if_sink_is_report(ccx, error);

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

    fn reject_if_sink_is_probe(&self) {
        use RejectedIfProbeState::*;

        match self.rejected_if_probe.get() {
            NotRejected => {
                // (fallthrough)
            }
            RejectedWhileAwaitingBind | RejectedAfterBound => return,
        }

        match self.target.get() {
            Some(target) => {
                target.reject_if_sink_is_probe();

                self.rejected_if_probe.set(RejectedAfterBound);
            }
            None => {
                self.rejected_if_probe.set(RejectedWhileAwaitingBind);
            }
        }
    }
}

// === Promise types === //

#[derive_where(Default)]
struct PromiseOrigin<'tcx, T> {
    target: PromiseBindSlot<'tcx, T>,
}

impl<'tcx, T> AnyPromiseBuilder<'tcx> for PromiseOrigin<'tcx, T> {
    type Error = T;

    fn bind_target(
        &self,
        ccx: &mut ClauseCx<'tcx>,
        target: BoundAnyPromiseTarget<'tcx, Self::Error>,
    ) {
        self.target.bind_target(ccx, target);
    }
}

struct PromiseJoiner<'tcx, T> {
    target: PromiseBindSlot<'tcx, Vec<T>>,
    err_resolutions: Vec<Option<T>>,
    all_resolutions_remaining: u32,
}

impl<'tcx, T> AnyPromiseBuilder<'tcx> for PromiseJoiner<'tcx, T> {
    type Error = Vec<T>;

    fn bind_target(
        &self,
        ccx: &mut ClauseCx<'tcx>,
        target: BoundAnyPromiseTarget<'tcx, Self::Error>,
    ) {
        self.target.bind_target(ccx, target);
    }
}

impl<'tcx, T> AnyPromiseTarget<'tcx> for PromiseJoiner<'tcx, T> {
    type Error = T;

    fn accept_once_if_sink_is_report(&self, _userdata: u32) {
        todo!()
    }

    fn reject_once_if_sink_is_report(
        &self,
        ccx: &mut ClauseCx<'tcx>,
        error: Self::Error,
        userdata: u32,
    ) {
        todo!()
    }

    fn reject_if_sink_is_probe(&self, userdata: u32) {
        todo!()
    }
}

struct PromiseMapper<'tcx, T, V, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, T) -> V,
{
    _ty: PhantomData<fn(T) -> T>,
    target: PromiseBindSlot<'tcx, V>,
    mapper: Cell<Option<F>>,
}

impl<'tcx, T, V, F> AnyPromiseBuilder<'tcx> for PromiseMapper<'tcx, T, V, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, T) -> V,
{
    type Error = V;

    fn bind_target(
        &self,
        ccx: &mut ClauseCx<'tcx>,
        target: BoundAnyPromiseTarget<'tcx, Self::Error>,
    ) {
        self.target.bind_target(ccx, target);
    }
}

impl<'tcx, T, V, F> AnyPromiseTarget<'tcx> for PromiseMapper<'tcx, T, V, F>
where
    F: FnOnce(&mut ClauseCx<'tcx>, T) -> V,
{
    type Error = T;

    fn accept_once_if_sink_is_report(&self, _userdata: u32) {
        self.target.accept_once_if_sink_is_report();
    }

    fn reject_once_if_sink_is_report(
        &self,
        ccx: &mut ClauseCx<'tcx>,
        error: Self::Error,
        _userdata: u32,
    ) {
        let error = self.mapper.take().unwrap()(ccx, error);

        self.target.reject_once_if_sink_is_report(ccx, error);
    }

    fn reject_if_sink_is_probe(&self, _userdata: u32) {
        self.target.reject_if_sink_is_probe();
    }
}
