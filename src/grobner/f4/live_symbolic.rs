use std::cell::Cell;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Policy {
    pub order_initial: bool,
    pub deduplicate: bool,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Report {
    pub initial_generators: usize,
    pub batches: usize,
    pub offered_seeds: usize,
    pub retained_seeds: usize,
    pub peak_seed_capacity: usize,
    pub peak_order_capacity: usize,
}

#[derive(Clone, Copy)]
struct State {
    policy: Policy,
    initial_count: usize,
    report: Report,
}

thread_local! {
    static ACTIVE: Cell<Option<State>> = const { Cell::new(None) };
}

/// Run a serial research policy in this thread, restoring any outer scope after unwinding.
/// `initial_count` is for direct symbolic calls; live F4 replaces it with its normalized input size.
pub fn with_policy<R>(policy: Policy, initial_count: usize, f: impl FnOnce() -> R) -> R {
    observe(policy, initial_count, f).0
}

/// As `with_policy`, returning seed traffic and temporary-container capacity observations.
pub fn observe<R>(policy: Policy, initial_count: usize, f: impl FnOnce() -> R) -> (R, Report) {
    struct Reset(Option<State>);
    impl Drop for Reset {
        fn drop(&mut self) {
            ACTIVE.set(self.0);
        }
    }
    let _reset = Reset(ACTIVE.replace(Some(State {
        policy,
        initial_count,
        report: Report {
            initial_generators: initial_count,
            ..Report::default()
        },
    })));
    let result = f();
    (result, ACTIVE.get().unwrap().report)
}

pub(crate) fn initialize(count: usize) {
    if let Some(mut state) = ACTIVE.get() {
        state.initial_count = count;
        state.report.initial_generators = count;
        ACTIVE.set(Some(state));
    }
}

pub(crate) fn config() -> Option<(Policy, usize)> {
    ACTIVE.get().map(|s| (s.policy, s.initial_count))
}

pub(crate) fn record(offered: usize, retained: usize, seed_capacity: usize, order_capacity: usize) {
    if let Some(mut state) = ACTIVE.get() {
        state.report.batches += 1;
        state.report.offered_seeds += offered;
        state.report.retained_seeds += retained;
        state.report.peak_seed_capacity = state.report.peak_seed_capacity.max(seed_capacity);
        state.report.peak_order_capacity = state.report.peak_order_capacity.max(order_capacity);
        ACTIVE.set(Some(state));
    }
}
