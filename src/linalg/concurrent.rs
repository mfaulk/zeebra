//! Experimental pivots remain immutable until scoped readers join; failures leave the input untouched.

use crate::{
    linalg::{
        sparse::{EliminationStatistics, SparseMatrix, SparseRow},
        DenseAccumulator,
    },
    FiniteField,
};
use std::{
    panic::{catch_unwind, AssertUnwindSafe},
    sync::{
        atomic::{AtomicBool, Ordering},
        Mutex, OnceLock,
    },
    time::Instant,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Schedule {
    Static,
    Dynamic,
}

#[derive(Clone, Copy, Debug)]
pub struct Config {
    pub workers: usize,
    pub schedule: Schedule,
    pub max_entries: usize,
    pub max_workspace_bytes: usize,
    pub measure_work: bool,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            workers: 1,
            schedule: Schedule::Dynamic,
            max_entries: usize::MAX,
            max_workspace_bytes: 256 * 1024 * 1024,
            measure_work: true,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    InvalidPrefix,
    InvalidWorkers,
    Entries { required: usize },
    Workspace { required: usize },
    Cancelled,
    WorkerPanicked,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Report {
    #[cfg(feature = "research-work")]
    pub work: super::work::PhaseWork,
    /// Algebraic counters are exact; `peak_nonzeros` is the conservative reservation upper bound.
    pub statistics: EliminationStatistics,
    pub successful_publications: usize,
    pub failed_publications: usize,
    pub products: usize,
    pub inherited_products: usize,
    pub discovered_products: usize,
    pub peak_reserved_entries: usize,
    pub workspace_bytes: usize,
    pub worker_rows: Vec<usize>,
    pub worker_ns: Vec<u64>,
    pub scheduling_ns: u64,
    pub publication_ns: u64,
    pub retry_products: usize,
}

#[derive(Clone, Copy)]
enum Event {
    Row,
    Claim {
        #[cfg_attr(not(test), allow(dead_code))]
        column: usize,
    },
}

struct Ledger {
    next: usize,
    live: usize,
    peak: usize,
}

struct Reservation<'a> {
    ledger: &'a Mutex<Ledger>,
    entries: usize,
}
impl Reservation<'_> {
    fn publish(&mut self, entries: usize) {
        let mut ledger = self.ledger.lock().unwrap();
        ledger.live = ledger.live - self.entries + entries;
        self.entries = 0;
    }
}
impl Drop for Reservation<'_> {
    fn drop(&mut self) {
        self.ledger.lock().unwrap().live -= self.entries;
    }
}

/// Opt-in forward discovery only; callers retain the ordinary backward pass and serial fallback.
///
/// Reserves original inputs, all published entries and two full-width rows per active task.
/// Dense capacity and publication arrays have a separate workspace-byte cap. No mutation is
/// committed until all workers succeed; cancellation, refusal and panic preserve `matrix`.
pub fn reduce<F: FiniteField + Send + Sync>(
    matrix: &mut SparseMatrix<F>,
    split: usize,
    config: &Config,
    cancel: &AtomicBool,
) -> Result<Report, Error> {
    reduce_hooked(matrix, split, config, cancel, &|_| {})
}

/// [`reduce`], callable from code generic over [`FiniteField`] alone.
///
/// The `Send + Sync` bound is proved where a handle is made — by a concrete field, through
/// [`FiniteField::concurrent_elimination`] — so generic callers such as F4 need not carry it and
/// a field that cannot provide it gets the serial path rather than a compile error.
pub struct Dispatch<F: FiniteField> {
    reduce: ReduceFn<F>,
    sweep: ReduceFn<F>,
}

type ReduceFn<F> = fn(&mut SparseMatrix<F>, usize, &Config, &AtomicBool) -> Result<Report, Error>;

impl<F: FiniteField> Clone for Dispatch<F> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<F: FiniteField> Copy for Dispatch<F> {}

impl<F: FiniteField + Send + Sync> Dispatch<F> {
    pub fn new() -> Self {
        Self {
            reduce: reduce::<F>,
            sweep: sweep::<F>,
        }
    }
}

impl<F: FiniteField + Send + Sync> Default for Dispatch<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: FiniteField> Dispatch<F> {
    /// As [`reduce`].
    ///
    /// # Errors
    /// As [`reduce`].
    pub fn reduce(
        self,
        matrix: &mut SparseMatrix<F>,
        split: usize,
        config: &Config,
        cancel: &AtomicBool,
    ) -> Result<Report, Error> {
        (self.reduce)(matrix, split, config, cancel)
    }

    /// As [`sweep`].
    ///
    /// # Errors
    /// As [`sweep`].
    pub fn sweep(
        self,
        matrix: &mut SparseMatrix<F>,
        split: usize,
        config: &Config,
        cancel: &AtomicBool,
    ) -> Result<Report, Error> {
        (self.sweep)(matrix, split, config, cancel)
    }
}

/// [`crate::linalg::echelon::sweep_rows_against_pivots`] on worker threads, in place.
///
/// Lower rows never meet each other and the upper block is only read, so each lower row's result
/// is the serial sweep's whatever the thread count or schedule. Unlike [`reduce`], rows are
/// rewritten as they finish: at every instant a lower row is its input, or that row partway
/// through its own ascending sweep, so after any refusal or cancellation the serial sweep
/// finishes the matrix to the identical result. Upper rows are never written.
///
/// Reserves every resident entry plus one full-width row per active worker, so the reported peak
/// is an upper bound on the live count; a reservation that would cross `max_entries` refuses.
pub fn sweep<F: FiniteField + Send + Sync>(
    matrix: &mut SparseMatrix<F>,
    split: usize,
    config: &Config,
    cancel: &AtomicBool,
) -> Result<Report, Error> {
    if config.workers == 0 {
        return Err(Error::InvalidWorkers);
    }
    if split > matrix.num_rows() {
        return Err(Error::InvalidPrefix);
    }
    if cancel.load(Ordering::Relaxed) {
        return Err(Error::Cancelled);
    }
    let columns = matrix.num_columns();
    let initial = matrix.nonzeros();
    let tasks = matrix.num_rows() - split;
    let workers = config.workers.min(tasks).max(1);
    let reserved_row = columns;
    // Refuse up front when even one round of reservations cannot fit, before any row moves.
    let first_round = workers
        .checked_mul(reserved_row)
        .and_then(|n| n.checked_add(initial))
        .ok_or(Error::Entries {
            required: usize::MAX,
        })?;
    if first_round > config.max_entries {
        return Err(Error::Entries {
            required: first_round,
        });
    }
    let workspace_bytes = workers
        .checked_mul(columns)
        .and_then(|n| n.checked_mul(std::mem::size_of::<F>()))
        .ok_or(Error::Workspace {
            required: usize::MAX,
        })?;
    if workspace_bytes > config.max_workspace_bytes {
        return Err(Error::Workspace {
            required: workspace_bytes,
        });
    }
    let mut known = vec![None; columns];
    let mut rank = 0;
    let mut zeros = 0;
    for index in 0..split {
        let row = matrix.row(index);
        if let Some(column) = row.leading_column() {
            if row.leading_coefficient() != Some(F::ONE) || known[column].replace(index).is_some() {
                return Err(Error::InvalidPrefix);
            }
            rank += 1;
        } else {
            zeros += 1;
        }
    }
    let (upper, lower) = matrix.rows_mut().split_at_mut(split);
    let upper: &[SparseRow<F>] = upper;
    // Small chunks under the dynamic schedule balance rows of very different cost; the static
    // schedule hands each worker one contiguous share.
    let chunk = match config.schedule {
        Schedule::Static => tasks.div_ceil(workers).max(1),
        Schedule::Dynamic => (tasks / (workers * 16)).clamp(1, 64),
    };
    let queue = Mutex::new(lower.chunks_mut(chunk));
    let ledger = Mutex::new(Ledger {
        next: 0,
        live: initial,
        peak: initial,
    });
    let failed = AtomicBool::new(false);
    let results = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|_| {
                let (queue, ledger, failed, known) = (&queue, &ledger, &failed, &known);
                crate::util::team::spawn(scope, move || {
                    let result = catch_unwind(AssertUnwindSafe(|| {
                        sweep_worker(upper, known, queue, ledger, failed, cancel, config)
                    }))
                    .unwrap_or(Err(Error::WorkerPanicked));
                    if result.is_err() {
                        failed.store(true, Ordering::Relaxed);
                    }
                    result
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|handle| handle.join().unwrap_or(Err(Error::WorkerPanicked)))
            .collect::<Vec<_>>()
    });
    if let Some(error) = results
        .iter()
        .filter_map(|result| result.as_ref().err())
        .find(|error| **error != Error::Cancelled)
    {
        return Err(error.clone());
    }
    if cancel.load(Ordering::Relaxed) || results.iter().any(Result::is_err) {
        return Err(Error::Cancelled);
    }
    let mut report = Report {
        peak_reserved_entries: ledger.lock().unwrap().peak,
        workspace_bytes,
        statistics: EliminationStatistics {
            initial_nonzeros: initial,
            rank,
            zero_rows: zeros,
            ..Default::default()
        },
        ..Default::default()
    };
    for worker in results.into_iter().map(Result::unwrap) {
        report.products += worker.products;
        report.statistics.row_operations += worker.statistics.row_operations;
        report.statistics.zero_rows += worker.statistics.zero_rows;
        report.worker_rows.extend(worker.worker_rows);
        report.worker_ns.extend(worker.worker_ns);
    }
    report.statistics.final_nonzeros = matrix.nonzeros();
    report.statistics.peak_nonzeros = report.peak_reserved_entries;
    Ok(report)
}

/// One [`sweep`] worker: claim chunks of lower rows until none remain.
fn sweep_worker<F: FiniteField>(
    upper: &[SparseRow<F>],
    known: &[Option<usize>],
    queue: &Mutex<std::slice::ChunksMut<'_, SparseRow<F>>>,
    ledger: &Mutex<Ledger>,
    failed: &AtomicBool,
    cancel: &AtomicBool,
    config: &Config,
) -> Result<Report, Error> {
    let started = Instant::now();
    let columns = known.len();
    let mut accumulator = DenseAccumulator::new(columns);
    let mut report = Report::default();
    let mut rows = 0;
    let stopped = || cancel.load(Ordering::Relaxed) || failed.load(Ordering::Relaxed);
    loop {
        let Some(chunk) = queue.lock().unwrap().next() else {
            break;
        };
        for slot in chunk {
            if stopped() {
                return Err(Error::Cancelled);
            }
            let mut reservation = {
                let mut state = ledger.lock().unwrap();
                let required = state.live.checked_add(columns).ok_or(Error::Entries {
                    required: usize::MAX,
                })?;
                if required > config.max_entries {
                    return Err(Error::Entries { required });
                }
                state.live = required;
                state.peak = state.peak.max(required);
                Reservation {
                    ledger,
                    entries: columns,
                }
            };
            let before = slot.nonzeros();
            accumulator.load(slot);
            let (operations, products) =
                accumulator.sweep(|column| known[column].map(|pivot| &upper[pivot]));
            report.statistics.row_operations += operations;
            report.products += products;
            let row = accumulator.take();
            report.statistics.zero_rows += usize::from(row.is_zero());
            // The input's entries leave as the result's arrive; the reservation is released.
            let after = row.nonzeros();
            *slot = row;
            {
                let mut state = ledger.lock().unwrap();
                state.live = state.live - before + after;
            }
            reservation.publish(0);
            rows += 1;
        }
    }
    report.worker_rows.push(rows);
    report
        .worker_ns
        .push(started.elapsed().as_nanos().min(u64::MAX as u128) as u64);
    Ok(report)
}

fn reduce_hooked<F: FiniteField + Send + Sync>(
    matrix: &mut SparseMatrix<F>,
    split: usize,
    config: &Config,
    cancel: &AtomicBool,
    hook: &(impl Fn(Event) + Sync),
) -> Result<Report, Error> {
    if config.workers == 0 {
        return Err(Error::InvalidWorkers);
    }
    if split > matrix.num_rows() {
        return Err(Error::InvalidPrefix);
    }
    if cancel.load(Ordering::Relaxed) {
        return Err(Error::Cancelled);
    }
    let columns = matrix.num_columns();
    let initial = matrix.nonzeros();
    if initial > config.max_entries {
        return Err(Error::Entries { required: initial });
    }
    let tasks = matrix.num_rows() - split;
    let workers = config.workers.min(tasks);
    let workspace_bytes = workers
        .checked_mul(columns)
        .and_then(|n| n.checked_mul(std::mem::size_of::<F>()))
        .and_then(|n| {
            columns
                .checked_mul(
                    std::mem::size_of::<OnceLock<(usize, SparseRow<F>)>>()
                        + std::mem::size_of::<Option<usize>>(),
                )
                .and_then(|m| n.checked_add(m))
        })
        .ok_or(Error::Workspace {
            required: usize::MAX,
        })?;
    if workspace_bytes > config.max_workspace_bytes {
        return Err(Error::Workspace {
            required: workspace_bytes,
        });
    }
    let mut known = vec![None; columns];
    let mut rank = 0;
    let mut zeros = 0;
    for index in 0..split {
        let row = matrix.row(index);
        if let Some(column) = row.leading_column() {
            if row.leading_coefficient() != Some(F::ONE) || known[column].replace(index).is_some() {
                return Err(Error::InvalidPrefix);
            }
            rank += 1;
        } else {
            zeros += 1;
        }
    }
    let slots: Vec<OnceLock<(usize, SparseRow<F>)>> =
        (0..columns).map(|_| OnceLock::new()).collect();
    let ledger = Mutex::new(Ledger {
        next: split,
        live: initial,
        peak: initial,
    });
    let failed = AtomicBool::new(false);
    let input: &SparseMatrix<F> = matrix;
    let results = std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for worker in 0..workers {
            let slots = &slots;
            let known = &known;
            let ledger = &ledger;
            let failed = &failed;
            handles.push(crate::util::team::spawn(scope, move || {
                let result = catch_unwind(AssertUnwindSafe(|| {
                    let run = || {
                        let started = Instant::now();
                        let mut accumulator = DenseAccumulator::new(columns);
                        let mut report = Report::default();
                        let mut rows = 0;
                        let mut index =
                            split + (tasks as u128 * worker as u128 / workers as u128) as usize;
                        let end = split
                            + (tasks as u128 * (worker + 1) as u128 / workers as u128) as usize;
                        loop {
                            if cancel.load(Ordering::Relaxed) || failed.load(Ordering::Relaxed) {
                                return Err(Error::Cancelled);
                            }
                            let scheduling = config.measure_work.then(Instant::now);
                            let (current, mut reservation) = {
                                let mut state = ledger.lock().unwrap();
                                let current = match config.schedule {
                                    Schedule::Static => {
                                        if index == end {
                                            break;
                                        }
                                        let current = index;
                                        index += 1;
                                        current
                                    }
                                    Schedule::Dynamic => {
                                        if state.next == input.num_rows() {
                                            break;
                                        }
                                        let current = state.next;
                                        state.next += 1;
                                        current
                                    }
                                };
                                let reserved = columns.checked_mul(2).ok_or(Error::Entries {
                                    required: usize::MAX,
                                })?;
                                let required =
                                    state.live.checked_add(reserved).ok_or(Error::Entries {
                                        required: usize::MAX,
                                    })?;
                                if required > config.max_entries {
                                    return Err(Error::Entries { required });
                                }
                                state.live = required;
                                state.peak = state.peak.max(required);
                                (
                                    current,
                                    Reservation {
                                        ledger,
                                        entries: reserved,
                                    },
                                )
                            };
                            if let Some(started) = scheduling {
                                report.scheduling_ns += started.elapsed().as_nanos() as u64;
                            }
                            hook(Event::Row);
                            accumulator.load(input.row(current));
                            let mut published = 0;
                            let mut retry = false;
                            loop {
                                if cancel.load(Ordering::Relaxed) || failed.load(Ordering::Relaxed)
                                {
                                    return Err(Error::Cancelled);
                                }
                                let Some(column) = accumulator.leading_column() else {
                                    report.statistics.zero_rows += 1;
                                    accumulator.take();
                                    break;
                                };
                                let pivot = known[column]
                                    .map(|index| input.row(index))
                                    .or_else(|| slots[column].get().map(|(_, row)| row));
                                if let Some(pivot) = pivot {
                                    let factor = accumulator.leading_coefficient().unwrap();
                                    accumulator.subtract_scaled(pivot, factor);
                                    report.statistics.row_operations += 1;
                                    if config.measure_work {
                                        report.products += pivot.nonzeros();
                                        if known[column].is_some() {
                                            report.inherited_products += pivot.nonzeros();
                                        } else {
                                            report.discovered_products += pivot.nonzeros();
                                        }
                                        if retry {
                                            report.retry_products += pivot.nonzeros();
                                        }
                                    }
                                } else {
                                    if accumulator.normalize() {
                                        report.statistics.pivot_inversions += 1;
                                    }
                                    let row = accumulator.take();
                                    let entries = row.nonzeros();
                                    hook(Event::Claim { column });
                                    if cancel.load(Ordering::Relaxed)
                                        || failed.load(Ordering::Relaxed)
                                    {
                                        return Err(Error::Cancelled);
                                    }
                                    let publication = config.measure_work.then(Instant::now);
                                    let claim = slots[column].set((current, row));
                                    if let Some(started) = publication {
                                        report.publication_ns +=
                                            started.elapsed().as_nanos() as u64;
                                    }
                                    match claim {
                                        Ok(()) => {
                                            published = entries;
                                            report.successful_publications += 1;
                                            break;
                                        }
                                        Err((_, row)) => {
                                            report.failed_publications += 1;
                                            retry = true;
                                            accumulator.load(&row);
                                        }
                                    }
                                }
                            }
                            reservation.publish(published);
                            rows += 1;
                        }
                        report.worker_rows.push(rows);
                        report
                            .worker_ns
                            .push(started.elapsed().as_nanos().min(u64::MAX as u128) as u64);
                        Ok(report)
                    };
                    #[cfg(feature = "research-work")]
                    if config.measure_work {
                        let (result, work) = super::work::measure(run);
                        return result.map(|mut report: Report| {
                            report.work = work.outside_batch.forward;
                            report
                        });
                    }
                    run()
                }))
                .unwrap_or(Err(Error::WorkerPanicked));
                if result.is_err() {
                    failed.store(true, Ordering::Relaxed);
                }
                result
            }));
        }
        handles
            .into_iter()
            .map(|handle| handle.join().unwrap_or(Err(Error::WorkerPanicked)))
            .collect::<Vec<_>>()
    });
    // Prefer the original failure over another worker observing cancellation.
    if let Some(error) = results
        .iter()
        .filter_map(|result| result.as_ref().err())
        .find(|error| **error != Error::Cancelled)
    {
        return Err(error.clone());
    }
    if cancel.load(Ordering::Relaxed) || results.iter().any(Result::is_err) {
        return Err(Error::Cancelled);
    }
    let mut report = Report {
        peak_reserved_entries: ledger.lock().unwrap().peak,
        workspace_bytes,
        statistics: EliminationStatistics {
            initial_nonzeros: initial,
            rank,
            zero_rows: zeros,
            ..Default::default()
        },
        ..Default::default()
    };
    for worker in results.into_iter().map(Result::unwrap) {
        report.successful_publications += worker.successful_publications;
        report.failed_publications += worker.failed_publications;
        report.products += worker.products;
        report.inherited_products += worker.inherited_products;
        report.discovered_products += worker.discovered_products;
        #[cfg(feature = "research-work")]
        report.work.accumulate(&worker.work);
        report.scheduling_ns += worker.scheduling_ns;
        report.publication_ns += worker.publication_ns;
        report.retry_products += worker.retry_products;
        report.statistics.row_operations += worker.statistics.row_operations;
        report.statistics.pivot_inversions += worker.statistics.pivot_inversions;
        report.statistics.zero_rows += worker.statistics.zero_rows;
        report.worker_rows.extend(worker.worker_rows);
        report.worker_ns.extend(worker.worker_ns);
    }
    for row in &mut matrix.rows_mut()[split..] {
        *row = SparseRow::default();
    }
    for slot in slots {
        if let Some((index, row)) = slot.into_inner() {
            matrix.rows_mut()[index] = row;
        }
    }
    report.statistics.rank += report.successful_publications;
    report.statistics.final_nonzeros = matrix.nonzeros();
    report.statistics.peak_nonzeros = report.peak_reserved_entries;
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fields::{Bn254Fr, Zp13, Zp2},
        linalg::sparse::reduced_row_echelon,
        One,
    };
    use std::sync::Barrier;

    fn fixture<F: FiniteField>() -> SparseMatrix<F> {
        SparseMatrix::new(
            7,
            vec![
                SparseRow::new(&[(0, F::ONE), (4, F::ONE)]),
                SparseRow::new(&[(1, F::ONE), (2, F::ONE), (5, F::ONE)]),
                SparseRow::new(&[(1, F::ONE), (3, F::ONE), (6, F::ONE)]),
                SparseRow::new(&[(0, F::ONE), (4, F::ONE)]),
                SparseRow::new(&[]),
                SparseRow::new(&[(2, F::ONE), (3, F::ONE)]),
            ],
        )
    }

    fn canonical<F: FiniteField>(mut matrix: SparseMatrix<F>) -> Vec<SparseRow<F>> {
        reduced_row_echelon(&mut matrix);
        let mut rows: Vec<_> = matrix
            .rows()
            .iter()
            .filter(|row| !row.is_zero())
            .cloned()
            .collect();
        rows.sort_by_key(SparseRow::leading_column);
        rows
    }

    // Static and dynamic schedules preserve full row spaces, inherited rows and worker counts across fields.
    #[test]
    fn row_space_and_fields() {
        fn check<F: FiniteField + Send + Sync>() {
            let input = fixture::<F>();
            let expected = canonical(input.clone());
            for schedule in [Schedule::Static, Schedule::Dynamic] {
                for workers in [1, 2, 4, 8] {
                    let mut matrix = input.clone();
                    let report = reduce(
                        &mut matrix,
                        1,
                        &Config {
                            workers,
                            schedule,
                            ..Config::default()
                        },
                        &AtomicBool::new(false),
                    )
                    .unwrap();
                    assert_eq!(matrix.row(0), input.row(0));
                    assert_eq!(canonical(matrix), expected);
                    assert_eq!(
                        report.worker_rows.iter().sum::<usize>(),
                        input.num_rows() - 1
                    );
                    assert_eq!(
                        report.statistics.rank + report.statistics.zero_rows,
                        input.num_rows()
                    );
                    assert!(report.products > 0);
                    #[cfg(feature = "research-work")]
                    {
                        assert_eq!(report.products, report.work.coefficient_products);
                        assert_eq!(
                            report.statistics.row_operations,
                            report.work.pivot_applications
                        );
                    }
                }
            }
        }
        check::<Zp13>();
        check::<Bn254Fr>();
        check::<Zp2>();
    }

    // Two workers forced to publish at one column retain the losing relation and advance its pivot.
    #[test]
    fn forced_publication_race() {
        for _ in 0..16 {
            let input = SparseMatrix::new(
                3,
                vec![
                    SparseRow::<Zp13>::new(&[(0, Zp13::ONE), (1, Zp13::ONE)]),
                    SparseRow::new(&[(0, Zp13::ONE), (2, Zp13::ONE)]),
                ],
            );
            let expected = canonical(input.clone());
            let mut matrix = input;
            let barrier = Barrier::new(2);
            let report = reduce_hooked(
                &mut matrix,
                0,
                &Config {
                    workers: 2,
                    ..Config::default()
                },
                &AtomicBool::new(false),
                &|event| {
                    if matches!(event, Event::Claim { column: 0, .. }) {
                        barrier.wait();
                    }
                },
            )
            .unwrap();
            assert_eq!(report.failed_publications, 1);
            assert_eq!(report.successful_publications, 2);
            assert_eq!(canonical(matrix), expected);
        }
    }

    // Entry/workspace refusals and cancellation leave the original matrix available for a clean retry.
    #[test]
    fn refusals_cancel_and_reuse() {
        let input = fixture::<Zp13>();
        let mut matrix = input.clone();
        for config in [
            Config {
                max_entries: input.nonzeros(),
                ..Config::default()
            },
            Config {
                max_workspace_bytes: 0,
                ..Config::default()
            },
            Config {
                max_entries: input.nonzeros() + 2 * input.num_columns() + 1,
                ..Config::default()
            },
            Config {
                workers: 0,
                ..Config::default()
            },
        ] {
            assert!(reduce(&mut matrix, 1, &config, &AtomicBool::new(false)).is_err());
            assert_eq!(matrix, input);
        }
        assert_eq!(
            reduce(&mut matrix, 1, &Config::default(), &AtomicBool::new(true)),
            Err(Error::Cancelled)
        );
        assert_eq!(matrix, input);
        reduce(&mut matrix, 1, &Config::default(), &AtomicBool::new(false)).unwrap();
        assert_eq!(canonical(matrix), canonical(input));
    }

    // A worker panic or cancellation during a claim discards every partial pivot and permits subsequent reuse.
    #[test]
    fn worker_failure_cleanup() {
        let input = fixture::<Zp13>();
        let mut matrix = input.clone();
        let cancel = AtomicBool::new(false);
        assert_eq!(
            reduce_hooked(
                &mut matrix,
                1,
                &Config {
                    workers: 2,
                    ..Config::default()
                },
                &cancel,
                &|_| panic!("worker failure")
            ),
            Err(Error::WorkerPanicked)
        );
        assert_eq!(matrix, input);
        assert_eq!(
            reduce_hooked(&mut matrix, 1, &Config::default(), &cancel, &|_| {
                cancel.store(true, Ordering::Relaxed);
            }),
            Err(Error::Cancelled)
        );
        assert_eq!(matrix, input);
        reduce(&mut matrix, 1, &Config::default(), &AtomicBool::new(false)).unwrap();
        assert_eq!(canonical(matrix), canonical(input));
    }

    // Empty and all-inherited matrices succeed without work, while invalid inherited pivots are rejected.
    #[test]
    fn empty_and_invalid_prefixes() {
        let mut empty = SparseMatrix::<Zp13>::new(0, vec![]);
        assert_eq!(
            reduce(&mut empty, 0, &Config::default(), &AtomicBool::new(false))
                .unwrap()
                .statistics
                .rank,
            0
        );
        let mut inherited = SparseMatrix::new(2, vec![SparseRow::<Zp13>::new(&[(0, Zp13::ONE)])]);
        assert_eq!(
            reduce(
                &mut inherited,
                1,
                &Config::default(),
                &AtomicBool::new(false)
            )
            .unwrap()
            .successful_publications,
            0
        );
        let mut invalid = SparseMatrix::new(2, vec![SparseRow::<Zp13>::new(&[(0, Zp13::new(2))])]);
        assert_eq!(
            reduce(&mut invalid, 1, &Config::default(), &AtomicBool::new(false)),
            Err(Error::InvalidPrefix)
        );
    }

    // Rectangular random and rank-deficient inputs agree coefficient-for-coefficient after independent RREF.
    #[test]
    fn rectangular_differential() {
        use rand::{Rng, SeedableRng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(728);
        for _ in 0..48 {
            let columns = rng.gen_range(1..20);
            let count = rng.gen_range(1..25);
            let rows = (0..count)
                .map(|_| {
                    SparseRow::<Zp13>::new(
                        &(0..columns)
                            .filter_map(|column| {
                                let value = rng.gen_range(0..13);
                                (value != 0).then_some((column, Zp13::new(value)))
                            })
                            .collect::<Vec<_>>(),
                    )
                })
                .collect();
            let input = SparseMatrix::new(columns, rows);
            let expected = canonical(input.clone());
            for schedule in [Schedule::Static, Schedule::Dynamic] {
                let mut matrix = input.clone();
                reduce(
                    &mut matrix,
                    0,
                    &Config {
                        workers: 4,
                        schedule,
                        ..Config::default()
                    },
                    &AtomicBool::new(false),
                )
                .unwrap();
                assert_eq!(canonical(matrix), expected);
            }
        }
    }

    // A digest-pinned live F4 matrix preserves its complete row space under every measured worker count.
    #[test]
    fn captured_corpus_row_space() {
        use crate::{
            fields::Mersenne31,
            grobner::{
                benchmark_systems::katsura,
                f4::{
                    matrix_corpus::{capture_matrix, corpus, BatchSelector},
                    F4Options,
                },
            },
            MonomialOrder,
        };
        let label = "katsura-7/grevlex/m31/default";
        let mut captured = capture_matrix(
            label,
            &katsura::<7, Mersenne31>(),
            MonomialOrder::GradedReverseLexicographic,
            &F4Options::default(),
            BatchSelector::Prefix(4),
        )
        .unwrap();
        let specs = corpus();
        let spec = specs.iter().find(|spec| spec.label == label).unwrap();
        assert_eq!(captured.fingerprint, spec.fingerprint);
        let split = captured.matrix.partition_reducers_first();
        let input = captured.matrix.matrix().clone();
        let expected = canonical(input.clone());
        for workers in [1, 2, 4, 8, 16, 32, 64] {
            for schedule in [Schedule::Static, Schedule::Dynamic] {
                let mut matrix = input.clone();
                reduce(
                    &mut matrix,
                    split,
                    &Config {
                        workers,
                        schedule,
                        ..Config::default()
                    },
                    &AtomicBool::new(false),
                )
                .unwrap();
                assert_eq!(canonical(matrix), expected);
            }
        }
    }

    /// An upper block in echelon form above random lower rows, over `columns` columns.
    fn sweep_fixture(seed: u64, columns: usize) -> (SparseMatrix<Zp13>, usize) {
        use crate::linalg::sparse::row_echelon;
        use rand::{Rng, SeedableRng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut random = |count: usize| {
            (0..count)
                .map(|_| {
                    SparseRow::<Zp13>::new(
                        &(0..columns)
                            .filter_map(|column| {
                                let value = rng.gen_range(0..13);
                                (value != 0 && rng.gen_bool(0.4))
                                    .then_some((column, Zp13::new(value)))
                            })
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let mut upper = SparseMatrix::new(columns, random(columns / 2));
        row_echelon(&mut upper);
        let mut rows: Vec<_> = upper
            .rows()
            .iter()
            .filter(|row| !row.is_zero())
            .cloned()
            .collect();
        let split = rows.len();
        rows.extend(random(30));
        (SparseMatrix::new(columns, rows), split)
    }

    // The concurrent sweep writes the serial sweep's rows, in place, for every worker count and schedule.
    #[test]
    fn sweep_matches_the_serial_sweep() {
        use crate::linalg::echelon::sweep_rows_against_pivots;
        for seed in 0..24 {
            let (input, split) = sweep_fixture(seed, 1 + seed as usize % 20);
            let mut expected = input.clone();
            let serial = sweep_rows_against_pivots(&mut expected, split, usize::MAX).unwrap();
            for schedule in [Schedule::Static, Schedule::Dynamic] {
                for workers in [1, 2, 4, 16] {
                    let mut matrix = input.clone();
                    let report = sweep(
                        &mut matrix,
                        split,
                        &Config {
                            workers,
                            schedule,
                            ..Config::default()
                        },
                        &AtomicBool::new(false),
                    )
                    .unwrap();
                    assert_eq!(matrix, expected, "seed {seed} {schedule:?} {workers}");
                    assert_eq!(report.statistics.rank, serial.rank);
                    assert_eq!(report.statistics.zero_rows, serial.zero_rows);
                    assert_eq!(report.statistics.row_operations, serial.row_operations);
                    assert_eq!(report.statistics.final_nonzeros, matrix.nonzeros());
                    assert!(report.peak_reserved_entries >= serial.peak_nonzeros.min(1));
                    assert_eq!(
                        report.worker_rows.iter().sum::<usize>(),
                        input.num_rows() - split
                    );
                }
            }
        }
    }

    // A refused or cancelled sweep leaves rows the serial sweep finishes to the identical result.
    #[test]
    fn sweep_refusals_leave_rows_the_serial_sweep_finishes() {
        use crate::linalg::echelon::sweep_rows_against_pivots;
        let (input, split) = sweep_fixture(7, 16);
        let mut expected = input.clone();
        sweep_rows_against_pivots(&mut expected, split, usize::MAX).unwrap();
        for config in [
            Config {
                workers: 4,
                max_entries: input.nonzeros() + 15,
                ..Config::default()
            },
            Config {
                workers: 4,
                max_workspace_bytes: 0,
                ..Config::default()
            },
            Config {
                workers: 0,
                ..Config::default()
            },
        ] {
            let mut matrix = input.clone();
            assert!(sweep(&mut matrix, split, &config, &AtomicBool::new(false)).is_err());
            assert_eq!(&matrix.rows()[..split], &input.rows()[..split]);
            sweep_rows_against_pivots(&mut matrix, split, usize::MAX).unwrap();
            assert_eq!(matrix, expected);
        }
        let mut matrix = input.clone();
        assert_eq!(
            sweep(
                &mut matrix,
                split,
                &Config::default(),
                &AtomicBool::new(true)
            ),
            Err(Error::Cancelled)
        );
        assert_eq!(matrix, input);
        let mut invalid = SparseMatrix::new(2, vec![SparseRow::<Zp13>::new(&[(0, Zp13::new(2))])]);
        assert_eq!(
            sweep(&mut invalid, 1, &Config::default(), &AtomicBool::new(false)),
            Err(Error::InvalidPrefix)
        );
    }

    // The sweep is reachable through a field's dispatch handle, as F4 reaches it.
    #[test]
    fn dispatch_reaches_the_sweep() {
        let (input, split) = sweep_fixture(3, 12);
        let mut expected = input.clone();
        crate::linalg::echelon::sweep_rows_against_pivots(&mut expected, split, usize::MAX)
            .unwrap();
        let mut matrix = input;
        Dispatch::<Zp13>::new()
            .sweep(
                &mut matrix,
                split,
                &Config {
                    workers: 3,
                    ..Config::default()
                },
                &AtomicBool::new(false),
            )
            .unwrap();
        assert_eq!(matrix, expected);
    }
}
