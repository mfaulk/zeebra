//! #940: the level-synchronous parallel closure of `docs/research/m32-parallel-symbolic.md` §2.
//!
//! Its output is the serial closure's exactly (§3): columns, rows in order, handles, and the
//! reducer cache afterwards. A level's contiguous slices are scanned by the team against `seen`,
//! `work` and the cache as they stood before the step; the caller merges the slices in order, with
//! the team parked at the barrier, so the scan holds only read guards, the merge the only write
//! guard, and no lock is ever contended. No `unsafe`.

use std::{
    cell::Cell,
    mem::{size_of, take},
    ops::Range,
    sync::{
        atomic::{AtomicUsize, Ordering::Relaxed},
        Barrier, Mutex, RwLock,
    },
    time::Instant,
};

#[cfg(test)]
use super::super::claim::Adversary;
use super::{least_ratio, Element, Row, RowSource, NONE};
use crate::{
    fields::ConcurrentJob,
    poly::{MonomialMap, MonomialOrder},
    FiniteField, Monomial,
};

pub(super) type Cache<const N: usize> = MonomialMap<N, (u32, u32)>;

const SLICES_PER_WORKER: usize = 4;
/// Marks a slice-local id in a scanned row; handles stay below it.
const LOCAL: u32 = 1 << 31;

/// When the team is woken. A level narrower than `min_frontier` is scanned by the caller alone
/// (#861's `MIN_FRONTIER`), and fewer than `min_sort` columns are sorted by it alone, so a closure
/// that never widens never starts a team. `fallback` (tests) takes the serial path a field that
/// cannot cross threads takes.
#[derive(Clone, Copy, Debug)]
pub(in crate::grobner::sigf4) struct Tuning {
    pub(in crate::grobner::sigf4) min_frontier: usize,
    pub(in crate::grobner::sigf4) min_sort: usize,
    pub(in crate::grobner::sigf4) fallback: bool,
}

impl Default for Tuning {
    fn default() -> Self {
        Self {
            min_frontier: 512,
            min_sort: 4096,
            fallback: false,
        }
    }
}

#[cfg(test)]
thread_local! {
    static TUNING: std::cell::Cell<Tuning> = std::cell::Cell::new(Tuning::default());
}

/// Runs `f` with `tuning` in force on this thread.
#[cfg(test)]
pub(in crate::grobner::sigf4) fn with_tuning<R>(tuning: Tuning, f: impl FnOnce() -> R) -> R {
    let old = TUNING.replace(tuning);
    let result = f();
    TUNING.set(old);
    result
}

pub(super) fn tuning() -> Tuning {
    #[cfg(test)]
    return TUNING.get();
    #[cfg(not(test))]
    Tuning::default()
}

/// One batch's matrix before elimination: columns descending, rows (targets, then reducers in
/// column order) and each row's column per term.
pub(super) struct Matrix<const N: usize> {
    pub(super) columns: Vec<Monomial<N>>,
    pub(super) rows: Vec<Row<N>>,
    pub(super) handles: Vec<Vec<u32>>,
    pub(super) reducers: usize,
    pub(super) team_levels: usize,
    pub(super) peak_live_bytes: usize,
}

impl<const N: usize> Matrix<N> {
    /// The closure's output, apart from how it was computed.
    pub(super) fn same(&self, other: &Self) -> bool {
        self.columns == other.columns
            && self.rows == other.rows
            && self.handles == other.handles
            && self.reducers == other.reducers
    }
}

/// Why a closure stopped at a level boundary (§3.1 T3–T5). A row stop is the serial engine's own
/// verdict: rows only grow, and the serial check reads rows first.
#[derive(Debug)]
pub(super) enum Halt {
    Rows,
    Wall,
    LiveBytes { bytes: usize },
}

pub(super) struct Closure<'a, const N: usize, F> {
    pub(super) order: MonomialOrder,
    pub(super) basis: &'a [Element<N, F>],
    pub(super) lead_masks: &'a [u64],
    pub(super) inputs: &'a [Vec<(Monomial<N>, F)>],
    pub(super) targets: &'a [Row<N>],
    pub(super) cache: &'a mut Cache<N>,
    pub(super) workers: usize,
    pub(super) max_rows: usize,
    pub(super) deadline: Option<Instant>,
    pub(super) live_limit: Option<usize>,
    pub(super) tuning: Tuning,
    #[cfg(test)]
    pub(super) adversary: Option<Adversary>,
}

/// The state a scan reads and the caller writes between steps.
#[derive(Default)]
struct State<const N: usize> {
    seen: MonomialMap<N, u32>,
    work: Vec<Monomial<N>>,
    cache: Cache<N>,
    /// Sorted runs of column ids, merged pairwise.
    runs: Vec<Mutex<Vec<u32>>>,
    position: Vec<u32>,
    /// Handle rows, cut into parts for renumbering.
    parts: Vec<Mutex<Vec<Vec<u32>>>>,
    /// Claim order → slice; the identity outside adverse-schedule tests.
    #[cfg(test)]
    claims: Vec<usize>,
}

/// What one slice of a level produced.
#[derive(Default)]
struct Slice<const N: usize> {
    /// Each row with its handles: one known before the step, or `LOCAL | local id`. The merge
    /// translates them in place, so a row's handles are allocated once.
    rows: Vec<(Row<N>, Vec<u32>)>,
    /// Handles across `rows`.
    refs: usize,
    new: Vec<Monomial<N>>,
    local: MonomialMap<N, u32>,
    updates: Vec<(Monomial<N>, (u32, u32))>,
}

impl<const N: usize> Slice<N> {
    fn bytes(&self) -> usize {
        let mono = size_of::<Monomial<N>>();
        self.rows.capacity() * size_of::<(Row<N>, Vec<u32>)>()
            + self.refs * 4
            + self.new.capacity() * mono
            + self.local.capacity() * (mono + 5)
            + self.updates.capacity() * (mono + 8)
    }
}

#[derive(Clone, Copy)]
enum Step {
    Scan {
        seeds: bool,
        lo: usize,
        hi: usize,
        chunk: usize,
    },
    Sort,
    Merge {
        stride: usize,
    },
    Renumber,
    Exit,
}

#[derive(Clone, Copy)]
struct Plan {
    step: Step,
    count: usize,
}

/// The team's rendezvous: the plan for the next step, its claim counter and the barrier.
struct Team {
    plan: Mutex<Plan>,
    next: AtomicUsize,
    barrier: Barrier,
}

/// What the caller accumulates; rows and handles in serial order.
struct Out<const N: usize> {
    rows: Vec<Row<N>>,
    handles: Vec<Vec<u32>>,
    refs: usize,
    reducers: usize,
}

impl<const N: usize, F: FiniteField> Closure<'_, N, F> {
    fn terms(&self, source: RowSource) -> &[(Monomial<N>, F)] {
        match source {
            RowSource::Input(i) => &self.inputs[i],
            RowSource::Element(id) => &self.basis[id as usize].terms,
        }
    }

    /// Item `item` of a level: its row, the lead handle of a reducer row, and the terms to shift;
    /// `None` for a column no element reduces. Also the cache entry the lookup computed, when the
    /// one read was missing or stale.
    #[allow(clippy::type_complexity)]
    fn item(
        &self,
        seeds: bool,
        item: usize,
        work: &[Monomial<N>],
        cache: &Cache<N>,
    ) -> (
        Option<(Row<N>, Option<u32>, &[(Monomial<N>, F)])>,
        Option<(Monomial<N>, (u32, u32))>,
    ) {
        if seeds {
            let t = &self.targets[item];
            let row = Row {
                sig: t.sig,
                mult: t.mult,
                source: t.source,
            };
            return (Some((row, None, self.terms(t.source))), None);
        }
        let m = work[item];
        let cached = cache.get(&m).copied();
        let (best, total) = least_ratio(self.basis, self.lead_masks, self.order, &m, cached);
        let update =
            (cached.map_or(0, |(_, scanned)| scanned) < total).then_some((m, (best, total)));
        if best == NONE {
            return (None, update);
        }
        let e = &self.basis[best as usize];
        let mult = m.checked_div(&e.lead).expect("the lead divides the column");
        let row = Row {
            sig: e.sig.times(&mult),
            mult,
            source: RowSource::Element(best),
        };
        (Some((row, Some(item as u32), &e.terms[1..])), update)
    }

    /// A narrow level on the caller, straight into the tables: the serial closure's own steps.
    fn direct(&self, state: &mut State<N>, seeds: bool, items: Range<usize>, out: &mut Out<N>) {
        let State {
            seen, work, cache, ..
        } = state;
        for item in items {
            let (found, update) = self.item(seeds, item, work, cache);
            if let Some((m, entry)) = update {
                cache.insert(m, entry);
            }
            let Some((row, lead, terms)) = found else {
                continue;
            };
            let mut handles = Vec::with_capacity(terms.len() + usize::from(lead.is_some()));
            handles.extend(lead);
            for (tm, _) in terms {
                let s = *tm * row.mult;
                handles.push(*seen.entry(s).or_insert_with(|| {
                    work.push(s);
                    (work.len() - 1) as u32
                }));
            }
            out.refs += handles.len();
            out.reducers += usize::from(!seeds);
            out.handles.push(handles);
            out.rows.push(row);
        }
    }

    /// One slice of a level, against the frozen state.
    fn scan(&self, state: &State<N>, seeds: bool, items: Range<usize>, out: &mut Slice<N>) {
        out.rows.clear();
        out.refs = 0;
        out.new.clear();
        out.local.clear();
        out.updates.clear();
        for item in items {
            let (found, update) = self.item(seeds, item, &state.work, &state.cache);
            out.updates.extend(update);
            let Some((row, lead, terms)) = found else {
                continue;
            };
            let mut handles = Vec::with_capacity(terms.len() + usize::from(lead.is_some()));
            handles.extend(lead);
            let (local, new) = (&mut out.local, &mut out.new);
            for (tm, _) in terms {
                let s = *tm * row.mult;
                handles.push(match state.seen.get(&s) {
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
            out.refs += handles.len();
            out.rows.push((row, handles));
        }
    }

    /// A slice's new monomials get their ids in local first-occurrence order (an earlier slice's
    /// id wins), its rows their translated refs, and the cache its updates (§3, Lemmas 2 and 4).
    fn merge(state: &mut State<N>, slice: &mut Slice<N>, out: &mut Out<N>, seeds: bool) {
        let State {
            seen, work, cache, ..
        } = state;
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
        if !seeds {
            out.reducers += slice.rows.len();
        }
        out.refs += slice.refs;
        for (row, mut handles) in slice.rows.drain(..) {
            for h in &mut handles {
                if *h & LOCAL != 0 {
                    *h = translate[(*h & !LOCAL) as usize];
                }
            }
            out.handles.push(handles);
            out.rows.push(row);
        }
        cache.extend(slice.updates.drain(..));
    }

    /// Claims and runs units of `plan` until none is left.
    fn help(
        &self,
        plan: Plan,
        state: &RwLock<State<N>>,
        slices: &[Mutex<Slice<N>>],
        next: &AtomicUsize,
    ) {
        let state = state.read().expect("no step panics");
        let order = self.order;
        loop {
            let k = next.fetch_add(1, Relaxed);
            if k >= plan.count {
                return;
            }
            match plan.step {
                Step::Scan {
                    seeds,
                    lo,
                    hi,
                    chunk,
                } => {
                    #[cfg(test)]
                    let k = {
                        if let Some(adversary) = &self.adversary {
                            pause(adversary, lo as u64, k as u64);
                        }
                        state.claims[k]
                    };
                    let start = lo + k * chunk;
                    let items = start..(start + chunk).min(hi);
                    let mut slice = slices[k].lock().expect("no scan panics");
                    self.scan(&state, seeds, items, &mut slice);
                }
                Step::Sort => {
                    let work = &state.work;
                    let mut run = state.runs[k].lock().expect("no sort panics");
                    run.sort_unstable_by(|&a, &b| order.cmp(&work[b as usize], &work[a as usize]));
                }
                Step::Merge { stride } => {
                    let (a, b) = (2 * k * stride, 2 * k * stride + stride);
                    if b < state.runs.len() {
                        let right = take(&mut *state.runs[b].lock().expect("no sort panics"));
                        let mut left = state.runs[a].lock().expect("no sort panics");
                        let merged = merge_runs(order, &state.work, &left, &right);
                        *left = merged;
                    }
                }
                Step::Renumber => {
                    let mut part = state.parts[k].lock().expect("no renumber panics");
                    for row in part.iter_mut() {
                        for h in row.iter_mut() {
                            *h = state.position[*h as usize];
                        }
                    }
                }
                Step::Exit => unreachable!("an exit plan is never helped"),
            }
        }
    }

    /// Bytes the batch's tables, rows and handles hold; the caller adds the slice scratch. The
    /// cache is the engine's, across batches, and is not charged here.
    fn live_bytes(state: &State<N>, out: &Out<N>) -> usize {
        let mono = size_of::<Monomial<N>>();
        state.seen.capacity() * (mono + 5)
            + state.work.capacity() * mono
            + out.rows.capacity() * size_of::<Row<N>>()
            + out.handles.capacity() * size_of::<Vec<u32>>()
            + out.refs * 4
    }

    /// The level-synchronous closure on `workers` threads (the caller included). One scoped team
    /// per batch, started at the first wide step and parked at the barrier between steps.
    pub(super) fn parallel(self) -> Result<Matrix<N>, Halt>
    where
        F: Sync,
    {
        let workers = self.workers.max(1);
        let state = RwLock::new(State {
            cache: take(&mut *self.cache),
            ..State::default()
        });
        let slices: Vec<Mutex<Slice<N>>> = (0..workers * SLICES_PER_WORKER)
            .map(|_| Mutex::default())
            .collect();
        let team = Team {
            plan: Mutex::new(Plan {
                step: Step::Exit,
                count: 0,
            }),
            next: AtomicUsize::new(0),
            barrier: Barrier::new(workers),
        };
        let mut out = Out {
            rows: Vec::with_capacity(self.targets.len()),
            handles: Vec::with_capacity(self.targets.len()),
            refs: 0,
            reducers: 0,
        };
        let (mut team_levels, mut peak) = (0, 0);
        let started = Cell::new(false);
        let (this, team, state_ref, slices_ref) = (&self, &team, &state, &slices[..]);
        let result = std::thread::scope(|scope| {
            let mut step = |plan: Plan| {
                if !started.replace(true) {
                    for _ in 1..workers {
                        scope.spawn(move || loop {
                            team.barrier.wait();
                            let plan = *team.plan.lock().expect("no plan panics");
                            if matches!(plan.step, Step::Exit) {
                                return;
                            }
                            this.help(plan, state_ref, slices_ref, &team.next);
                            team.barrier.wait();
                        });
                    }
                }
                *team.plan.lock().expect("no plan panics") = plan;
                team.next.store(0, Relaxed);
                team.barrier.wait();
                this.help(plan, state_ref, slices_ref, &team.next);
                team.barrier.wait();
            };
            let halted = this.levels(
                state_ref,
                slices_ref,
                &mut out,
                &mut step,
                &mut team_levels,
                &mut peak,
            );
            let result = match halted {
                Some(halt) => Err(halt),
                None => Ok(this.sort(state_ref, &mut out, &mut step)),
            };
            if started.get() {
                team.plan.lock().expect("no plan panics").step = Step::Exit;
                team.barrier.wait();
            }
            result
        });
        *self.cache = state.into_inner().expect("no step panics").cache;
        Ok(Matrix {
            columns: result?,
            rows: out.rows,
            handles: out.handles,
            reducers: out.reducers,
            team_levels,
            peak_live_bytes: peak,
        })
    }

    /// The closure's levels, each scanned (by the team when wide) and merged; checks the bounds
    /// at every level boundary.
    fn levels(
        &self,
        state: &RwLock<State<N>>,
        slices: &[Mutex<Slice<N>>],
        out: &mut Out<N>,
        step: &mut impl FnMut(Plan),
        team_levels: &mut usize,
        peak: &mut usize,
    ) -> Option<Halt> {
        let workers = self.workers.max(1);
        let (mut seeds, mut lo, mut hi) = (true, 0, self.targets.len());
        let mut scratch = 0;
        #[cfg(test)]
        let mut level = 0u64;
        while lo < hi {
            let n = hi - lo;
            let count = if workers > 1 && n >= self.tuning.min_frontier {
                let chunk = n.div_ceil(slices.len().min(n));
                let count = n.div_ceil(chunk);
                #[cfg(test)]
                {
                    state.write().expect("no step panics").claims =
                        claims(self.adversary.as_ref(), count, level);
                }
                step(Plan {
                    step: Step::Scan {
                        seeds,
                        lo,
                        hi,
                        chunk,
                    },
                    count,
                });
                *team_levels += 1;
                count
            } else {
                0
            };
            #[cfg(test)]
            if let Some(adversary) = &self.adversary {
                pause(adversary, u64::MAX - level, count as u64);
            }
            let mut guard = state.write().expect("no step panics");
            if count == 0 {
                self.direct(&mut guard, seeds, lo..hi, out);
            }
            for slice in &slices[..count] {
                Self::merge(
                    &mut guard,
                    &mut slice.lock().expect("no scan panics"),
                    out,
                    seeds,
                );
            }
            (seeds, lo, hi) = (false, if seeds { 0 } else { hi }, guard.work.len());
            #[cfg(test)]
            {
                level += 1;
            }
            if out.rows.len() > self.max_rows {
                return Some(Halt::Rows);
            }
            if count > 0 {
                scratch = slices
                    .iter()
                    .map(|s| s.lock().expect("no scan panics").bytes())
                    .sum();
            }
            let bytes = Self::live_bytes(&guard, out) + scratch;
            *peak = (*peak).max(bytes);
            if self.live_limit.is_some_and(|limit| bytes > limit) {
                return Some(Halt::LiveBytes { bytes });
            }
            if self.deadline.is_some_and(|d| Instant::now() >= d) {
                return Some(Halt::Wall);
            }
            #[cfg(test)]
            if self
                .adversary
                .and_then(|a| a.cancel_after)
                .is_some_and(|after| level >= after)
            {
                return Some(Halt::Wall);
            }
        }
        None
    }

    /// Columns descending and handles renumbered to positions; on the team when there are many
    /// columns. The order is total and the columns distinct, so any correct sort gives the serial
    /// permutation (§3, Lemma 5).
    fn sort(
        &self,
        state: &RwLock<State<N>>,
        out: &mut Out<N>,
        step: &mut impl FnMut(Plan),
    ) -> Vec<Monomial<N>> {
        let workers = self.workers.max(1);
        let order = self.order;
        let mut guard = state.write().expect("no step panics");
        let n = guard.work.len();
        let team = workers > 1 && n >= self.tuning.min_sort;
        let by_position: Vec<u32> = if team {
            let runs = workers.min(n);
            let chunk = n.div_ceil(runs);
            guard.runs = (0..runs)
                .map(|r| {
                    Mutex::new(((r * chunk) as u32..((r + 1) * chunk).min(n) as u32).collect())
                })
                .collect();
            drop(guard);
            step(Plan {
                step: Step::Sort,
                count: runs,
            });
            let mut stride = 1;
            while stride < runs {
                step(Plan {
                    step: Step::Merge { stride },
                    count: runs.div_ceil(2 * stride),
                });
                stride *= 2;
            }
            guard = state.write().expect("no step panics");
            let runs = take(&mut guard.runs);
            runs.into_iter()
                .next()
                .map(|r| r.into_inner().expect("no sort panics"))
                .unwrap_or_default()
        } else {
            let work = &guard.work;
            let mut ids: Vec<u32> = (0..n as u32).collect();
            ids.sort_unstable_by(|&a, &b| order.cmp(&work[b as usize], &work[a as usize]));
            ids
        };
        let mut position = vec![0u32; n];
        for (k, &id) in by_position.iter().enumerate() {
            position[id as usize] = k as u32;
        }
        let columns: Vec<Monomial<N>> = by_position
            .iter()
            .map(|&id| guard.work[id as usize])
            .collect();
        if team {
            let rows = out.handles.len();
            let per = rows.div_ceil(workers * SLICES_PER_WORKER).max(1);
            let mut handles = take(&mut out.handles).into_iter();
            guard.parts = (0..rows.div_ceil(per))
                .map(|_| Mutex::new(handles.by_ref().take(per).collect()))
                .collect();
            guard.position = position;
            let count = guard.parts.len();
            drop(guard);
            step(Plan {
                step: Step::Renumber,
                count,
            });
            let mut guard = state.write().expect("no step panics");
            out.handles = take(&mut guard.parts)
                .into_iter()
                .flat_map(|p| p.into_inner().expect("no renumber panics"))
                .collect();
        } else {
            for row in &mut out.handles {
                for h in row.iter_mut() {
                    *h = position[*h as usize];
                }
            }
        }
        columns
    }
}

/// Two descending runs of distinct column ids, merged.
fn merge_runs<const N: usize>(
    order: MonomialOrder,
    work: &[Monomial<N>],
    a: &[u32],
    b: &[u32],
) -> Vec<u32> {
    let mut merged = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        if order.cmp(&work[b[j] as usize], &work[a[i] as usize]) == std::cmp::Ordering::Greater {
            merged.push(b[j]);
            j += 1;
        } else {
            merged.push(a[i]);
            i += 1;
        }
    }
    merged.extend_from_slice(&a[i..]);
    merged.extend_from_slice(&b[j..]);
    merged
}

impl<const N: usize, F: FiniteField> ConcurrentJob<F> for Closure<'_, N, F> {
    type Output = Result<Matrix<N>, Halt>;

    fn run(self) -> Self::Output
    where
        F: Send + Sync,
    {
        self.parallel()
    }
}

#[cfg(test)]
fn mix(seed: u64, a: u64, b: u64) -> u64 {
    let mut z = seed ^ a.rotate_left(32) ^ b.wrapping_mul(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Seeded yields, as the cascade's adversary takes them.
#[cfg(test)]
fn pause(adversary: &Adversary, a: u64, b: u64) {
    let draw = mix(adversary.seed, a, b);
    if draw % 1000 < adversary.yield_permille {
        for _ in 0..1 + (draw >> 40) % 8 {
            std::thread::yield_now();
        }
    }
}

/// The order slices are claimed in: reversed and/or seeded-shuffled under an adversary.
#[cfg(test)]
fn claims(adversary: Option<&Adversary>, count: usize, level: u64) -> Vec<usize> {
    let mut order: Vec<usize> = (0..count).collect();
    if let Some(adversary) = adversary {
        if adversary.reverse {
            order.reverse();
        }
        if adversary.seed != 0 {
            for i in (1..count).rev() {
                let j = (mix(adversary.seed, level, i as u64) % (i as u64 + 1)) as usize;
                order.swap(i, j);
            }
        }
    }
    order
}
