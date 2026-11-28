//! #933's replay of the symbolic stage: on every batch, the level-synchronous closure of
//! `docs/research/m32-parallel-symbolic.md` §2 runs beside the engine's serial closure on the same
//! targets, basis and reducer cache, is asserted equal to it (columns, rows in order, handles and the
//! cache afterwards), and is timed at each worker count.
//!
//! It only observes: the engine's closure builds the matrix, the prototype's output is compared and
//! dropped, and no prototype run is on the engine's stage clocks. Its timings are a ceiling for the
//! design, not a measurement of #940: the column sort here is serial, and each run starts from a
//! cache clone taken off the clock. Recording is per thread, as `replay` is.

use std::{
    cell::RefCell,
    ops::Range,
    sync::{
        atomic::{AtomicUsize, Ordering::Relaxed},
        Barrier, Mutex, RwLock,
    },
    time::{Duration, Instant},
};

use super::{least_ratio, Element, Row, RowSource, NONE};
use crate::{
    fields::ConcurrentJob,
    poly::{MonomialMap, MonomialOrder},
    FiniteField, Monomial,
};

/// The worker counts each batch is replayed at.
pub const WORKERS: [usize; 4] = [1, 4, 8, 16];
/// Runs per worker count; the median-time run is kept.
const REPS: usize = 3;
const SLICES_PER_WORKER: usize = 4;
/// Marks a slice-local id in a scanned row; handles stay below it.
const LOCAL: u32 = 1 << 31;

thread_local! {
    static ACTIVE: RefCell<Option<(usize, Vec<SymbolicRecord>)>> = const { RefCell::new(None) };
}

/// Runs `f` with recording on for this thread and returns one record per batch. A level with
/// fewer than `min_frontier` items is scanned by the caller alone, as #861's closure does.
pub fn record<R>(min_frontier: usize, f: impl FnOnce() -> R) -> (R, Vec<SymbolicRecord>) {
    ACTIVE.with(|a| *a.borrow_mut() = Some((min_frontier.max(1), Vec::new())));
    let result = f();
    let records = ACTIVE
        .with(|a| a.borrow_mut().take())
        .map_or_else(Vec::new, |(_, r)| r);
    (result, records)
}

pub(super) fn active() -> bool {
    ACTIVE.with(|a| a.borrow().is_some())
}

/// One prototype run's clocks, in nanoseconds.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Run {
    pub workers: usize,
    pub total: u64,
    /// The levels' scans: parallel on a wide level, the caller's alone on a narrow one.
    pub scan: u64,
    /// The ordered merges: serial by design.
    pub merge: u64,
    /// Column sort and handle renumbering: serial here, parallel in the design.
    pub sort: u64,
}

/// A serial pass's breakdown: what the reducer search costs, and how the cache served it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Census {
    /// Inside `least_ratio`, cache read included.
    pub lookup_ns: u64,
    pub cache_current: u64,
    pub cache_stale: u64,
    pub cache_missing: u64,
    /// Basis elements the lookups scanned.
    pub elements_scanned: u64,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SymbolicRecord {
    pub targets: usize,
    pub rows: usize,
    pub columns: usize,
    /// Items per level, the targets first.
    pub levels: Vec<usize>,
    /// The engine's own closure on this batch.
    pub serial_ns: u64,
    pub census: Census,
    /// One per [`WORKERS`] entry.
    pub runs: Vec<Run>,
}

pub(super) struct View<'a, const N: usize, F> {
    pub order: MonomialOrder,
    pub basis: &'a [Element<N, F>],
    pub lead_masks: &'a [u64],
    pub inputs: &'a [Vec<(Monomial<N>, F)>],
}

impl<const N: usize, F> Clone for View<'_, N, F> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<const N: usize, F> Copy for View<'_, N, F> {}

type Cache<const N: usize> = MonomialMap<N, (u32, u32)>;

/// The serial closure's columns, rows and handles, and its cache afterwards.
pub(super) type Serial<'a, const N: usize> = (
    &'a [Monomial<N>],
    &'a [Row<N>],
    &'a [Vec<u32>],
    &'a Cache<N>,
);

/// Replays one batch at every worker count, asserting each run's output equal to `serial`.
/// Skipped for a field that cannot cross threads.
pub(super) fn replay<const N: usize, F: FiniteField>(
    view: View<'_, N, F>,
    targets: &[Row<N>],
    before: &Cache<N>,
    serial: Serial<'_, N>,
    serial_time: Duration,
) {
    let min_frontier = ACTIVE.with(|a| a.borrow().as_ref().map_or(1, |(m, _)| *m));
    let job = |workers, census| Job {
        view,
        targets,
        cache: before,
        workers,
        min_frontier,
        census,
    };
    let mut record = SymbolicRecord {
        targets: targets.len(),
        rows: serial.1.len(),
        columns: serial.0.len(),
        serial_ns: serial_time.as_nanos() as u64,
        ..SymbolicRecord::default()
    };
    for workers in WORKERS {
        let mut runs = Vec::with_capacity(REPS);
        for _ in 0..REPS {
            let Ok((output, run, levels, _)) = F::run_concurrent(job(workers, false)) else {
                return;
            };
            assert_same(&output, serial, workers);
            record.levels = levels;
            runs.push(run);
        }
        runs.sort_by_key(|r| r.total);
        record.runs.push(runs.swap_remove(REPS / 2));
    }
    if let Ok((output, _, _, census)) = F::run_concurrent(job(1, true)) {
        assert_same(&output, serial, 1);
        record.census = census;
    }
    ACTIVE.with(|a| {
        if let Some((_, records)) = a.borrow_mut().as_mut() {
            records.push(record);
        }
    });
}

struct Output<const N: usize> {
    columns: Vec<Monomial<N>>,
    rows: Vec<Row<N>>,
    handles: Vec<Vec<u32>>,
    cache: Cache<N>,
}

fn assert_same<const N: usize>(output: &Output<N>, serial: Serial<'_, N>, workers: usize) {
    let (columns, rows, handles, cache) = serial;
    let at = |what| format!("the {workers}-worker closure moved the {what}");
    assert!(output.columns == columns, "{}", at("columns"));
    assert_eq!(output.rows.len(), rows.len(), "{}", at("row count"));
    for (a, b) in output.rows.iter().zip(rows) {
        assert!(
            a.sig == b.sig && a.mult == b.mult && a.source == b.source,
            "{}",
            at("rows")
        );
    }
    assert!(output.handles == handles, "{}", at("handles"));
    assert!(output.cache == *cache, "{}", at("reducer cache"));
}

/// The state a scan reads and the merge writes, with the team parked.
struct Shared<const N: usize> {
    seen: MonomialMap<N, u32>,
    work: Vec<Monomial<N>>,
    cache: Cache<N>,
}

/// What one slice of a level produced.
#[derive(Default)]
struct Slice<const N: usize> {
    /// Each row with the end of its refs.
    rows: Vec<(Row<N>, usize)>,
    /// A handle known before the step, or `LOCAL | local id`.
    refs: Vec<u32>,
    new: Vec<Monomial<N>>,
    local: MonomialMap<N, u32>,
    updates: Vec<(Monomial<N>, (u32, u32))>,
    census: Census,
}

struct Job<'a, const N: usize, F> {
    view: View<'a, N, F>,
    targets: &'a [Row<N>],
    cache: &'a Cache<N>,
    workers: usize,
    min_frontier: usize,
    census: bool,
}

/// A level: the targets (`seeds`) or the columns `items` of `work`.
#[derive(Clone, Copy)]
struct Plan {
    seeds: bool,
    lo: usize,
    hi: usize,
    chunk: usize,
    count: usize,
    exit: bool,
}

impl<const N: usize, F: FiniteField> Job<'_, N, F> {
    fn scan(&self, shared: &Shared<N>, seeds: bool, items: Range<usize>, out: &mut Slice<N>) {
        out.rows.clear();
        out.refs.clear();
        out.new.clear();
        out.local.clear();
        out.updates.clear();
        let view = &self.view;
        for item in items {
            let (row, lead, terms) = if seeds {
                let t = &self.targets[item];
                let terms = match t.source {
                    RowSource::Input(i) => &view.inputs[i][..],
                    RowSource::Element(id) => view.basis[id as usize].terms.full(),
                };
                let row = Row {
                    sig: t.sig,
                    mult: t.mult,
                    source: t.source,
                };
                (row, None, terms)
            } else {
                let m = shared.work[item];
                let cached = shared.cache.get(&m).copied();
                let clock = self.census.then(Instant::now);
                let (best, total) =
                    least_ratio(view.basis, view.lead_masks, view.order, &m, cached);
                let scanned = cached.map_or(0, |(_, s)| s);
                if let Some(clock) = clock {
                    let c = &mut out.census;
                    c.lookup_ns += clock.elapsed().as_nanos() as u64;
                    c.elements_scanned += u64::from(total - scanned);
                    match cached {
                        None => c.cache_missing += 1,
                        Some(_) if scanned < total => c.cache_stale += 1,
                        Some(_) => c.cache_current += 1,
                    }
                }
                if scanned < total {
                    out.updates.push((m, (best, total)));
                }
                if best == NONE {
                    continue;
                }
                let e = &view.basis[best as usize];
                let mult = m.checked_div(&e.lead).expect("the lead divides the column");
                let row = Row {
                    sig: e.sig.times(&mult),
                    mult,
                    source: RowSource::Element(best),
                };
                (row, Some(item as u32), &e.terms.full()[1..])
            };
            out.refs.extend(lead);
            let (local, new) = (&mut out.local, &mut out.new);
            for (tm, _) in terms {
                let s = *tm * row.mult;
                out.refs.push(match shared.seen.get(&s) {
                    Some(&h) => h,
                    None => {
                        let next = new.len() as u32;
                        LOCAL
                            | *local.entry(s).or_insert_with(|| {
                                new.push(s);
                                next
                            })
                    }
                });
            }
            out.rows.push((row, out.refs.len()));
        }
    }

    /// Slices in order: new monomials get their handles, rows their translated refs.
    fn merge(shared: &mut Shared<N>, slice: &mut Slice<N>, out: &mut Output<N>) {
        let Shared { seen, work, cache } = shared;
        let translate: Vec<u32> = slice
            .new
            .iter()
            .map(|&m| {
                *seen.entry(m).or_insert_with(|| {
                    work.push(m);
                    (work.len() - 1) as u32
                })
            })
            .collect();
        assert!(
            work.len() < LOCAL as usize,
            "handles stay below the local mark"
        );
        let mut start = 0;
        for (row, end) in slice.rows.drain(..) {
            let refs = &slice.refs[start..end];
            let resolve = |&r: &u32| match r & LOCAL {
                0 => r,
                _ => translate[(r & !LOCAL) as usize],
            };
            out.handles.push(refs.iter().map(resolve).collect());
            out.rows.push(row);
            start = end;
        }
        cache.extend(slice.updates.drain(..));
    }

    /// Claims slices of the planned level until none is left.
    fn work(
        &self,
        plan: Plan,
        shared: &RwLock<Shared<N>>,
        slices: &[Mutex<Slice<N>>],
        next: &AtomicUsize,
    ) {
        let shared = shared.read().expect("no scan panics");
        loop {
            let k = next.fetch_add(1, Relaxed);
            if k >= plan.count {
                return;
            }
            let lo = plan.lo + k * plan.chunk;
            let items = lo..(lo + plan.chunk).min(plan.hi);
            self.scan(
                &shared,
                plan.seeds,
                items,
                &mut slices[k].lock().expect("no scan panics"),
            );
        }
    }

    #[allow(clippy::type_complexity)]
    fn closure(&self) -> (Output<N>, Run, Vec<usize>, Census)
    where
        F: Sync,
    {
        let workers = self.workers.max(1);
        let shared = RwLock::new(Shared {
            seen: MonomialMap::default(),
            work: Vec::new(),
            cache: self.cache.clone(),
        });
        let slices: Vec<Mutex<Slice<N>>> = (0..workers * SLICES_PER_WORKER)
            .map(|_| Mutex::default())
            .collect();
        let plan = Mutex::new(Plan {
            seeds: true,
            lo: 0,
            hi: 0,
            chunk: 0,
            count: 0,
            exit: false,
        });
        let (next, barrier) = (AtomicUsize::new(0), Barrier::new(workers));
        let mut out = Output {
            columns: Vec::new(),
            rows: Vec::with_capacity(self.targets.len()),
            handles: Vec::with_capacity(self.targets.len()),
            cache: MonomialMap::default(),
        };
        let (mut run, mut levels) = (Run::default(), Vec::new());
        let started = Instant::now();
        std::thread::scope(|scope| {
            let mut members = Vec::new();
            for _ in 1..workers {
                members.push(crate::util::team::spawn(scope, || loop {
                    barrier.wait();
                    let p = *plan.lock().expect("no plan panics");
                    if p.exit {
                        return;
                    }
                    self.work(p, &shared, &slices, &next);
                    barrier.wait();
                }));
            }
            let (mut seeds, mut lo, mut hi) = (true, 0, self.targets.len());
            while lo < hi {
                let n = hi - lo;
                levels.push(n);
                let clock = Instant::now();
                let count = if workers == 1 || n < self.min_frontier {
                    let shared = shared.read().expect("no scan panics");
                    let mut slice = slices[0].lock().expect("no scan panics");
                    self.scan(&shared, seeds, lo..hi, &mut slice);
                    1
                } else {
                    let chunk = n.div_ceil(slices.len().min(n));
                    let p = Plan {
                        seeds,
                        lo,
                        hi,
                        chunk,
                        count: n.div_ceil(chunk),
                        exit: false,
                    };
                    *plan.lock().expect("no plan panics") = p;
                    next.store(0, Relaxed);
                    barrier.wait();
                    self.work(p, &shared, &slices, &next);
                    barrier.wait();
                    p.count
                };
                run.scan += clock.elapsed().as_nanos() as u64;
                let clock = Instant::now();
                let mut shared = shared.write().expect("no merge panics");
                for slice in &slices[..count] {
                    Self::merge(
                        &mut shared,
                        &mut slice.lock().expect("no scan panics"),
                        &mut out,
                    );
                }
                run.merge += clock.elapsed().as_nanos() as u64;
                (seeds, lo, hi) = (false, if seeds { 0 } else { hi }, shared.work.len());
            }
            plan.lock().expect("no plan panics").exit = true;
            if workers > 1 {
                barrier.wait();
            }
            crate::util::team::join_all(members);
        });
        let clock = Instant::now();
        let Shared { work, cache, .. } = shared.into_inner().expect("no merge panics");
        let order = self.view.order;
        let mut by_position: Vec<u32> = (0..work.len() as u32).collect();
        by_position.sort_unstable_by(|&a, &b| order.cmp(&work[b as usize], &work[a as usize]));
        let mut position = vec![0u32; work.len()];
        for (k, &id) in by_position.iter().enumerate() {
            position[id as usize] = k as u32;
        }
        for row in &mut out.handles {
            for h in row.iter_mut() {
                *h = position[*h as usize];
            }
        }
        out.columns = by_position.iter().map(|&id| work[id as usize]).collect();
        out.cache = cache;
        run.sort = clock.elapsed().as_nanos() as u64;
        run.total = started.elapsed().as_nanos() as u64;
        run.workers = workers;
        // A census pass is serial, so every level's census accumulated in slice 0.
        let census = slices[0].lock().expect("no scan panics").census.clone();
        (out, run, levels, census)
    }
}

impl<const N: usize, F: FiniteField> ConcurrentJob<F> for Job<'_, N, F> {
    #[allow(clippy::type_complexity)]
    type Output = (Output<N>, Run, Vec<usize>, Census);

    fn run(self) -> Self::Output
    where
        F: Send + Sync,
    {
        self.closure()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fields::PrimeFieldElement64,
        grobner::sigf4::{sig_f4_reported, SigF4Options},
        MultivariatePolynomial,
    };

    type Goldilocks = PrimeFieldElement64<18446744069414584321>;

    fn katsura4() -> Vec<MultivariatePolynomial<4, Goldilocks>> {
        let names = ["x0", "x1", "x2", "x3"];
        [
            "x0 + 2*x1 + 2*x2 + 2*x3 - 1",
            "x0^2 + 2*x1^2 + 2*x2^2 + 2*x3^2 - x0",
            "2*x0*x1 + 2*x1*x2 + 2*x2*x3 - x1",
            "x1^2 + 2*x0*x2 + 2*x1*x3 - x2",
        ]
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect()
    }

    // Every batch is replayed at every worker count with the team on every level, each run equal
    // to the serial closure (asserted inside), and recording leaves the basis unchanged.
    #[test]
    fn test_parallel_closure_reproduces_every_batch() {
        let system = katsura4();
        let order = MonomialOrder::GradedReverseLexicographic;
        let options = SigF4Options::default();
        let (plain, _) = sig_f4_reported(&system, order, &options);
        let ((recorded, stats), records) = record(1, || sig_f4_reported(&system, order, &options));
        assert_eq!(recorded.unwrap(), plain.unwrap());
        assert_eq!(records.len(), stats.batches);
        for r in &records {
            assert_eq!(
                r.runs.iter().map(|r| r.workers).collect::<Vec<_>>(),
                WORKERS
            );
            assert_eq!(r.levels[0], r.targets);
            assert!(r.columns > 0 && r.rows >= r.targets);
        }
        let looked_up = |r: &SymbolicRecord| r.census.cache_missing + r.census.cache_stale;
        assert!(records.iter().map(looked_up).sum::<u64>() > 0);
    }

    // Nothing is recorded outside `record`.
    #[test]
    fn test_inactive_replay_records_nothing() {
        assert!(!active());
        let (_, records) = record(1, || ());
        assert!(records.is_empty() && !active());
    }
}
