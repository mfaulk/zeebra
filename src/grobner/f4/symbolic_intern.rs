//! #860 research prototypes: symbolic preprocessing with the monomial interner off the serial path.
//!
//! The FIFO closure runs as breadth-first levels (#827). Each level, and the seed rows before the
//! first, is one *step*: workers scan slices of the step (covered check, divisor search, term
//! shift), look every term up in the interner as it stood before the step, and deduplicate the
//! unknown ones locally, pre-hashed, giving each a slice-local id in first-occurrence order. A
//! merge then gives each new monomial its handle. Handles must come out exactly as the serial
//! closure assigns them, and they do: the serial order of first occurrence is slice order, then
//! local first-occurrence order within the slice, which is the order both merges below respect.
//!
//! - [`Merge::Serial`] walks the slices' new monomials in that order on one thread, probing one
//!   table with the hash the worker already computed. Local ids map to handles through a
//!   per-slice translation array, so there is no rewrite pass over the arena.
//! - [`Merge::Sharded`] routes each new monomial to a hash shard. Shard workers find each
//!   monomial's first occurrence (its *owner*) in parallel; a prefix sum over the slices' owner
//!   counts then gives every owner its handle as `base[slice] + rank`, and each shard records
//!   handles for the monomials it holds. The global order is restored by arithmetic, not by a
//!   serial walk.
//!
//! Either way a final per-slice pass writes `term_handles` from the translation arrays. One worker
//! team is spawned per batch, not per level; levels smaller than `min_frontier` run on the caller
//! alone with the team parked, and batches with fewer than `min_seed_rows` seed rows never start
//! a team and take the shipping serial closure.
//!
//! Matrix construction sorts columns by monomial and reducer rows by leading column, so only the
//! *set* of reducer rows and the pair rows' order reach the matrix; exact handle identity is kept
//! here so the result can be compared with `==`, not because the matrix needs it.
use std::{
    collections::{HashMap, HashSet},
    hash::{BuildHasher, BuildHasherDefault, Hash, Hasher},
    sync::{
        atomic::{AtomicBool, AtomicU32, AtomicUsize, Ordering::Relaxed},
        Barrier, Mutex, RwLock,
    },
    time::{Duration, Instant},
};

use super::{
    options::{PairMultiples, ReducerSelection},
    symbolic::{
        symbolic_preprocessing_seeded, BuildMonomialHasher, MonicBasis, MonomialHandle,
        MonomialSet, Preprocessed, PreprocessedRow, ReducerCache, RowBudgetExceeded, RowKind,
        SymbolicCounts,
    },
};
use crate::{grobner::pairs::CriticalPair, FiniteField, Monomial};

/// How a step's new monomials receive their handles.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Merge {
    /// One thread, one table, slices in order.
    Serial,
    /// One shard per worker; ownership in parallel, handles by prefix sum.
    Sharded,
}

/// The prototypes' dispatch knobs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InternConfig {
    /// Threads in the team, the caller included.
    pub workers: usize,
    /// Which merge.
    pub merge: Merge,
    /// A level with fewer monomials runs on the caller alone.
    pub min_frontier: usize,
    /// Slices per worker, claimed dynamically, so an uneven frontier does not leave the team
    /// waiting on one slice.
    pub slices_per_worker: usize,
    /// A batch with fewer seed rows takes the shipping serial closure.
    pub min_seed_rows: usize,
}

/// Where a prototype's time went. Clocks are read per phase, never per monomial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct InternReport {
    /// The batch took the shipping serial closure.
    pub serial_fallback: bool,
    /// Steps: the seed step plus every level.
    pub steps: usize,
    /// Steps run on the team rather than on the caller alone.
    pub dispatched_steps: usize,
    /// Monomials that missed the pre-step interner, summed over slices (cross-slice repeats
    /// counted once per slice).
    pub candidates: usize,
    /// Of those, the monomials that were new to the step: the columns.
    pub owners: usize,
    /// The largest shard's share of a dispatched step's candidates, as a ratio to the mean, in
    /// thousandths, maximized over steps. 1000 is perfect balance.
    pub worst_shard_imbalance_milli: usize,
    /// Spawning the team.
    pub spawn: Duration,
    /// Seed rows: the pair loop and the seed-key set.
    pub seed: Duration,
    /// Scan phase: divisor search, term shift, interner lookup, local deduplication.
    pub scan: Duration,
    /// Merge phase (both merges), owner ranking and shard recording included.
    pub merge: Duration,
    /// Writing `term_handles` from the translation arrays.
    pub emit: Duration,
    /// The caller's serial stitching between phases: rows, leads, arena, `term_handles` appends.
    pub stitch: Duration,
}

/// A monomial carrying the hash a worker already computed, so the merge does not hash it again.
#[derive(Clone, Copy, Debug)]
struct Keyed<const N: usize> {
    hash: u64,
    monomial: Monomial<N>,
}

impl<const N: usize> PartialEq for Keyed<N> {
    fn eq(&self, other: &Self) -> bool {
        self.monomial == other.monomial
    }
}
impl<const N: usize> Eq for Keyed<N> {}
impl<const N: usize> Hash for Keyed<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

/// Passes a precomputed hash through unchanged.
#[derive(Default)]
struct PassThrough(u64);
impl Hasher for PassThrough {
    fn write(&mut self, _: &[u8]) {
        unreachable!("only precomputed hashes are written")
    }
    fn write_u64(&mut self, value: u64) {
        self.0 = value;
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

type Table<const N: usize> = HashMap<Keyed<N>, u32, BuildHasherDefault<PassThrough>>;

/// Bits 32.. pick the shard: hashbrown indexes buckets by the low bits and tags by the top seven.
fn shard_of(hash: u64, shards: usize) -> usize {
    ((hash >> 32) as usize) % shards
}

const LOCAL: u32 = 1 << 31;

/// One slice's scan output, kept across steps so its buffers are reused.
#[derive(Default)]
struct Slice<const N: usize> {
    /// Rows found: basis index, multiplier, frontier position + 1, end of its run in `refs`.
    rows: Vec<(usize, Monomial<N>, usize, usize)>,
    /// One per term: a handle, or `LOCAL | id` into `candidates`.
    refs: Vec<u32>,
    /// Pre-step misses, deduplicated within the slice, in first-occurrence order.
    candidates: Vec<Keyed<N>>,
    /// Per shard, the candidate ids it holds, ascending.
    by_shard: Vec<Vec<u32>>,
    local: Table<N>,
    counts: SymbolicCounts,
    /// Local id to handle, filled by the merge.
    translate: Vec<AtomicU32>,
    /// Whether this slice holds the step's first occurrence of the candidate.
    owner: Vec<AtomicBool>,
    /// Emit output: this slice's run of `term_handles`.
    handles: Vec<MonomialHandle>,
    /// Emit output: max over rows of (owners so far in the slice - frontier position).
    pending_peak: i64,
    /// Owners in local order, written by the sharded merge's ranking.
    new: Vec<Monomial<N>>,
}

/// One shard of the interner: monomial to an index into `handles`.
#[derive(Default)]
struct Shard<const N: usize> {
    table: Table<N>,
    handles: Vec<MonomialHandle>,
    /// This step: owners as (slice, local id), and repeats as (slice, local id, owner index).
    owners: Vec<(u32, u32)>,
    aliases: Vec<(u32, u32, u32)>,
    /// Owners per slice this step.
    per_slice: Vec<u32>,
}

/// Everything a phase reads; the caller mutates it only between phases, with the team parked.
struct Step<'a, const N: usize, F: FiniteField> {
    basis: &'a MonicBasis<N, F>,
    selection: ReducerSelection,
    lcms: &'a MonomialSet<N>,
    /// The monomials to scan (a level) — or empty, for the seed step, which shifts `seeds`.
    frontier: Vec<Monomial<N>>,
    seeds: Vec<(usize, Monomial<N>)>,
    chunk: usize,
    shards: Vec<RwLock<Shard<N>>>,
    slices: Vec<RwLock<Slice<N>>>,
    /// Owners in earlier slices, for the sharded ranking.
    bases: Vec<u32>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Job {
    Scan,
    Own,
    Rank,
    Record,
    Emit,
    Exit,
}

/// The per-batch team: `run` executes a job's tasks on every member and returns when all are done.
struct Team {
    barrier: Option<Barrier>,
    job: Mutex<Job>,
    next: AtomicUsize,
}

impl Team {
    fn tasks(&self, job: Job, slices: usize, shards: usize) -> usize {
        match job {
            Job::Scan | Job::Rank | Job::Emit => slices,
            Job::Own | Job::Record => shards,
            Job::Exit => 0,
        }
    }
}

fn work<const N: usize, F: FiniteField>(team: &Team, step: &RwLock<Step<'_, N, F>>, job: Job) {
    let step = step.read().unwrap();
    let total = team.tasks(job, step.slices.len(), step.shards.len());
    loop {
        let task = team.next.fetch_add(1, Relaxed);
        if task >= total {
            return;
        }
        match job {
            Job::Scan => scan(&step, task),
            Job::Own => own(&step, task),
            Job::Rank => rank(&step, task),
            Job::Record => record(&step, task),
            Job::Emit => emit(&step, task),
            Job::Exit => unreachable!(),
        }
    }
}

fn lookup<const N: usize>(shards: &[&Shard<N>], key: &Keyed<N>) -> Option<MonomialHandle> {
    let shard = shards[shard_of(key.hash, shards.len())];
    shard.table.get(key).map(|&j| shard.handles[j as usize])
}

/// Scan one slice: rows, their terms, pre-step lookups, local deduplication.
fn scan<const N: usize, F: FiniteField>(step: &Step<'_, N, F>, task: usize) {
    let mut slice = step.slices[task].write().unwrap();
    let slice = &mut *slice;
    let shards: Vec<_> = step.shards.iter().map(|s| s.read().unwrap()).collect();
    let shards: Vec<&Shard<N>> = shards.iter().map(|g| &**g).collect();
    slice.rows.clear();
    slice.refs.clear();
    slice.candidates.clear();
    slice.local.clear();
    slice.by_shard.resize_with(shards.len(), Vec::new);
    slice.by_shard.iter_mut().for_each(Vec::clear);
    slice.counts = SymbolicCounts::default();
    let start = task * step.chunk;
    let push_terms = |slice: &mut Slice<N>, index: usize, multiplier: &Monomial<N>| {
        for (term, _) in step.basis.shifted_terms(index, multiplier) {
            let key = Keyed {
                hash: BuildMonomialHasher.hash_one(term),
                monomial: term,
            };
            let r = match lookup(&shards, &key) {
                Some(handle) => handle,
                None => {
                    let next = slice.candidates.len() as u32;
                    let id = *slice.local.entry(key).or_insert(next);
                    if id == next {
                        slice.candidates.push(key);
                        slice.by_shard[shard_of(key.hash, shards.len())].push(id);
                    }
                    LOCAL | id
                }
            };
            slice.refs.push(r);
        }
    };
    if step.frontier.is_empty() {
        let end = (start + step.chunk).min(step.seeds.len());
        for (offset, (index, multiplier)) in step.seeds[start.min(end)..end].iter().enumerate() {
            push_terms(slice, *index, multiplier);
            slice
                .rows
                .push((*index, *multiplier, start + offset + 1, slice.refs.len()));
        }
    } else {
        let end = (start + step.chunk).min(step.frontier.len());
        for (offset, monomial) in step.frontier[start.min(end)..end].iter().enumerate() {
            if step.lcms.contains(monomial) {
                continue;
            }
            let Some((index, multiplier)) =
                step.basis
                    .find_divisor_with(monomial, step.selection, &mut slice.counts)
            else {
                continue;
            };
            push_terms(slice, index, &multiplier);
            slice
                .rows
                .push((index, multiplier, start + offset + 1, slice.refs.len()));
        }
    }
    let n = slice.candidates.len();
    slice.translate.clear();
    slice.translate.resize_with(n, || AtomicU32::new(0));
    slice.owner.clear();
    slice.owner.resize_with(n, || AtomicBool::new(false));
}

/// Sharded merge, phase one: within shard `s`, find each new monomial's first occurrence.
fn own<const N: usize, F: FiniteField>(step: &Step<'_, N, F>, s: usize) {
    let mut shard = step.shards[s].write().unwrap();
    let shard = &mut *shard;
    shard.owners.clear();
    shard.aliases.clear();
    shard.per_slice.clear();
    shard.per_slice.resize(step.slices.len(), 0);
    let first = shard.handles.len() as u32;
    for (k, slice) in step.slices.iter().enumerate() {
        let slice = slice.read().unwrap();
        for &id in &slice.by_shard[s] {
            let key = slice.candidates[id as usize];
            let next = first + shard.owners.len() as u32;
            let j = *shard.table.entry(key).or_insert(next);
            if j == next {
                shard.owners.push((k as u32, id));
                shard.per_slice[k] += 1;
                slice.owner[id as usize].store(true, Relaxed);
            } else {
                shard.aliases.push((k as u32, id, j - first));
            }
        }
    }
}

/// Sharded merge, phase two: number slice `k`'s owners from its base, in local order.
fn rank<const N: usize, F: FiniteField>(step: &Step<'_, N, F>, k: usize) {
    let mut slice = step.slices[k].write().unwrap();
    let slice = &mut *slice;
    slice.new.clear();
    let mut handle = step.bases[k];
    for (id, owner) in slice.owner.iter().enumerate() {
        if owner.load(Relaxed) {
            slice.translate[id].store(handle, Relaxed);
            slice.new.push(slice.candidates[id].monomial);
            handle += 1;
        }
    }
}

/// Sharded merge, phase three: shard `s` records its owners' handles and resolves its repeats.
fn record<const N: usize, F: FiniteField>(step: &Step<'_, N, F>, s: usize) {
    let mut shard = step.shards[s].write().unwrap();
    let shard = &mut *shard;
    let slices: Vec<_> = step.slices.iter().map(|m| m.read().unwrap()).collect();
    let base = shard.handles.len();
    for &(k, id) in &shard.owners {
        let handle = slices[k as usize].translate[id as usize].load(Relaxed);
        shard.handles.push(handle);
    }
    for &(k, id, j) in &shard.aliases {
        let handle = shard.handles[base + j as usize];
        slices[k as usize].translate[id as usize].store(handle, Relaxed);
    }
}

/// Write slice `k`'s run of `term_handles`, and its contribution to the pending-queue peak.
fn emit<const N: usize, F: FiniteField>(step: &Step<'_, N, F>, k: usize) {
    let mut slice = step.slices[k].write().unwrap();
    let slice = &mut *slice;
    slice.handles.clear();
    slice.pending_peak = i64::MIN;
    let (mut seen, mut owned, mut at) = (0u32, 0i64, 0usize);
    for &(_, _, position, end) in &slice.rows {
        for &r in &slice.refs[at..end] {
            slice.handles.push(if r & LOCAL == 0 {
                r
            } else {
                let id = r & !LOCAL;
                if id == seen {
                    seen += 1;
                    owned += i64::from(slice.owner[id as usize].load(Relaxed));
                }
                slice.translate[id as usize].load(Relaxed)
            });
        }
        at = end;
        slice.pending_peak = slice.pending_peak.max(owned - position as i64);
    }
}

/// [`symbolic_preprocessing_seeded`] (uncached), with the interner off the serial path.
///
/// The result equals the serial closure's — rows, columns, handles and counters — and so does a
/// refusal: a closure is a least fixed point, so its row count does not depend on the order it is
/// discovered in, and checking the budget after each step refuses exactly the batches the serial
/// closure refuses. See the module documentation for the method.
///
/// # Panics
/// As [`symbolic_preprocessing_seeded`].
pub fn symbolic_preprocessing_interned<const N: usize, F: FiniteField + Sync>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
    max_rows: usize,
    selection: ReducerSelection,
    multiples: PairMultiples,
    config: &InternConfig,
) -> (Result<Preprocessed<N>, RowBudgetExceeded>, InternReport) {
    let mut report = InternReport::default();
    let seeding = Instant::now();
    let mut keys: Option<HashSet<(usize, Monomial<N>), BuildMonomialHasher>> = (multiples
        == PairMultiples::Distinct)
        .then(|| HashSet::with_capacity_and_hasher(2 * pairs.len(), BuildMonomialHasher));
    let mut rows: Vec<PreprocessedRow<N>> = Vec::with_capacity(2 * pairs.len());
    let mut counts = SymbolicCounts::default();
    let mut lcms: MonomialSet<N> = MonomialSet::default();
    for (position, pair) in pairs.iter().enumerate() {
        for basis_index in [pair.left, pair.right] {
            let multiplier = pair
                .lcm
                .checked_div(&basis.element(basis_index).leading_monomial)
                .expect("a pair's lcm is divisible by each of its leading monomials");
            if keys
                .as_mut()
                .is_some_and(|k| !k.insert((basis_index, multiplier)))
            {
                counts.pair_multiples_removed += 1;
                continue;
            }
            rows.push(PreprocessedRow {
                multiplier,
                basis_index,
                kind: RowKind::PairComponent { pair: position },
            });
        }
        lcms.insert(pair.lcm);
    }
    drop(keys);
    report.seed = seeding.elapsed();

    if config.workers <= 1 || rows.len() < config.min_seed_rows {
        report.serial_fallback = true;
        let result = symbolic_preprocessing_seeded(
            basis,
            pairs,
            max_rows,
            selection,
            &mut ReducerCache::disabled(),
            multiples,
        );
        return (result, report);
    }
    if rows.len() > max_rows {
        return (Err(RowBudgetExceeded { limit: max_rows }), report);
    }

    let workers = config.workers;
    let slice_count = workers * config.slices_per_worker.max(1);
    let shard_count = match config.merge {
        Merge::Serial => 1,
        Merge::Sharded => workers,
    };
    let seeds: Vec<(usize, Monomial<N>)> =
        rows.iter().map(|r| (r.basis_index, r.multiplier)).collect();
    let step = RwLock::new(Step {
        basis,
        selection,
        lcms: &lcms,
        frontier: Vec::new(),
        seeds,
        chunk: 0,
        shards: (0..shard_count).map(|_| RwLock::default()).collect(),
        slices: (0..slice_count).map(|_| RwLock::default()).collect(),
        bases: vec![0; slice_count],
    });
    let team = Team {
        barrier: Some(Barrier::new(workers)),
        job: Mutex::new(Job::Exit),
        next: AtomicUsize::new(0),
    };
    let solo = Team {
        barrier: None,
        job: Mutex::new(Job::Exit),
        next: AtomicUsize::new(0),
    };

    let mut monomials: Vec<Monomial<N>> = Vec::new();
    let mut term_handles: Vec<MonomialHandle> = Vec::new();
    let mut leads = lcms.clone();
    let mut refused = false;

    std::thread::scope(|scope| {
        let spawning = Instant::now();
        for _ in 1..workers {
            let (team, step) = (&team, &step);
            scope.spawn(move || {
                let barrier = team.barrier.as_ref().unwrap();
                loop {
                    barrier.wait();
                    let job = *team.job.lock().unwrap();
                    if job == Job::Exit {
                        return;
                    }
                    work(team, step, job);
                    barrier.wait();
                }
            });
        }
        report.spawn = spawning.elapsed();

        // Run `job` on the team (dispatched) or on the caller alone.
        let run = |job: Job, dispatched: bool, clock: &mut Duration| {
            let started = Instant::now();
            let t = if dispatched { &team } else { &solo };
            t.next.store(0, Relaxed);
            *t.job.lock().unwrap() = job;
            if let Some(barrier) = &t.barrier {
                barrier.wait();
                work(t, &step, job);
                barrier.wait();
            } else {
                work(t, &step, job);
            }
            *clock += started.elapsed();
        };

        let mut seed_step = true;
        loop {
            let level_start = monomials.len();
            let dispatched;
            {
                let mut s = step.write().unwrap();
                let size = if seed_step {
                    s.seeds.len()
                } else {
                    s.frontier.len()
                };
                if size == 0 {
                    break;
                }
                dispatched = size >= config.min_frontier;
                s.chunk = size.div_ceil(if dispatched { slice_count } else { 1 });
            }
            report.steps += 1;
            report.dispatched_steps += usize::from(dispatched);

            run(Job::Scan, dispatched, &mut report.scan);

            // Merge.
            let merging = Instant::now();
            match config.merge {
                Merge::Serial => {
                    let s = step.read().unwrap();
                    let mut shard = s.shards[0].write().unwrap();
                    let shard = &mut *shard;
                    for slice in &s.slices {
                        let mut slice = slice.write().unwrap();
                        let slice = &mut *slice;
                        report.candidates += slice.candidates.len();
                        slice.new.clear();
                        for (id, key) in slice.candidates.iter().enumerate() {
                            let next = shard.handles.len() as u32;
                            let j = *shard.table.entry(*key).or_insert(next);
                            if j == next {
                                let handle =
                                    MonomialHandle::try_from(monomials.len() + slice.new.len())
                                        .ok()
                                        .filter(|h| h & LOCAL == 0)
                                        .expect("fewer distinct monomials than a handle can name");
                                shard.handles.push(handle);
                                slice.owner[id].store(true, Relaxed);
                                slice.translate[id].store(handle, Relaxed);
                                slice.new.push(key.monomial);
                            } else {
                                slice.owner[id].store(false, Relaxed);
                                slice.translate[id].store(shard.handles[j as usize], Relaxed);
                            }
                        }
                        monomials.extend_from_slice(&slice.new);
                    }
                    report.merge += merging.elapsed();
                }
                Merge::Sharded => {
                    {
                        let s = step.read().unwrap();
                        for slice in &s.slices {
                            report.candidates += slice.read().unwrap().candidates.len();
                        }
                    }
                    let mut clock = Duration::ZERO;
                    run(Job::Own, dispatched, &mut clock);
                    {
                        let mut s = step.write().unwrap();
                        let s = &mut *s;
                        let per_shard: Vec<usize> = s
                            .shards
                            .iter()
                            .map(|sh| {
                                sh.read().unwrap().owners.len() + sh.read().unwrap().aliases.len()
                            })
                            .collect();
                        let total: usize = per_shard.iter().sum();
                        if dispatched && total > 0 {
                            let worst =
                                per_shard.iter().max().unwrap() * 1000 * per_shard.len() / total;
                            report.worst_shard_imbalance_milli =
                                report.worst_shard_imbalance_milli.max(worst);
                        }
                        let mut base = monomials.len();
                        for k in 0..s.slices.len() {
                            s.bases[k] = MonomialHandle::try_from(base)
                                .ok()
                                .filter(|h| h & LOCAL == 0)
                                .expect("fewer distinct monomials than a handle can name");
                            base += s
                                .shards
                                .iter()
                                .map(|sh| sh.read().unwrap().per_slice[k] as usize)
                                .sum::<usize>();
                        }
                    }
                    run(Job::Rank, dispatched, &mut clock);
                    run(Job::Record, dispatched, &mut clock);
                    report.merge += merging.elapsed();
                    let stitching = Instant::now();
                    let s = step.read().unwrap();
                    for slice in &s.slices {
                        monomials.extend_from_slice(&slice.read().unwrap().new);
                    }
                    report.stitch += stitching.elapsed();
                }
            }

            run(Job::Emit, dispatched, &mut report.emit);

            // Stitch: rows, leads, handles, counters, the next frontier.
            let stitching = Instant::now();
            let mut s = step.write().unwrap();
            let s = &mut *s;
            let width = if seed_step {
                s.seeds.len()
            } else {
                s.frontier.len()
            } as i64;
            let mut admitted_before = 0i64;
            let mut peak = if seed_step {
                0
            } else {
                counts.max_pending_monomials as i64
            };
            for slice in &s.slices {
                let slice = slice.read().unwrap();
                counts.add(&slice.counts);
                counts.monomials_enqueued += slice.refs.len();
                term_handles.extend_from_slice(&slice.handles);
                if !seed_step {
                    for &(basis_index, multiplier, position, _) in &slice.rows {
                        leads.insert(s.frontier[position - 1]);
                        rows.push(PreprocessedRow {
                            multiplier,
                            basis_index,
                            kind: RowKind::Reducer,
                        });
                    }
                    if !slice.rows.is_empty() {
                        peak = peak.max(width + admitted_before + slice.pending_peak);
                    }
                }
                admitted_before += slice.new.len() as i64;
            }
            report.owners += monomials.len() - level_start;
            if seed_step {
                counts.max_pending_monomials = monomials.len() - level_start;
                seed_step = false;
            } else {
                counts.max_pending_monomials = peak as usize;
            }
            s.frontier.clear();
            s.frontier.extend_from_slice(&monomials[level_start..]);
            report.stitch += stitching.elapsed();
            if rows.len() > max_rows {
                refused = true;
                break;
            }
        }

        *team.job.lock().unwrap() = Job::Exit;
        if workers > 1 {
            team.barrier.as_ref().unwrap().wait();
        }
    });

    if refused {
        return (Err(RowBudgetExceeded { limit: max_rows }), report);
    }
    (
        Ok(Preprocessed {
            rows,
            leading_monomials: leads,
            monomials,
            term_handles,
            counts,
        }),
        report,
    )
}

thread_local! {
    static LIVE: std::cell::Cell<Option<(InternConfig, InternReport)>> =
        const { std::cell::Cell::new(None) };
}

/// Run `f` with live F4 on this thread taking [`symbolic_preprocessing_interned`] under `config`,
/// and return the reports of every batch it served, summed.
pub fn with_live<R>(config: InternConfig, f: impl FnOnce() -> R) -> (R, InternReport) {
    struct Reset(Option<(InternConfig, InternReport)>);
    impl Drop for Reset {
        fn drop(&mut self) {
            LIVE.set(self.0);
        }
    }
    let reset = Reset(LIVE.replace(Some((config, InternReport::default()))));
    let result = f();
    let report = LIVE.get().expect("set above").1;
    drop(reset);
    (result, report)
}

fn accumulate(total: &mut InternReport, batch: &InternReport) {
    total.serial_fallback |= batch.serial_fallback;
    total.steps += batch.steps;
    total.dispatched_steps += batch.dispatched_steps;
    total.candidates += batch.candidates;
    total.owners += batch.owners;
    total.worst_shard_imbalance_milli = total
        .worst_shard_imbalance_milli
        .max(batch.worst_shard_imbalance_milli);
    total.spawn += batch.spawn;
    total.seed += batch.seed;
    total.scan += batch.scan;
    total.merge += batch.merge;
    total.emit += batch.emit;
    total.stitch += batch.stitch;
}

struct LiveJob<'a, const N: usize, F: FiniteField> {
    basis: &'a MonicBasis<N, F>,
    pairs: &'a [CriticalPair<N>],
    max_rows: usize,
    selection: ReducerSelection,
    multiples: PairMultiples,
    config: InternConfig,
}

impl<const N: usize, F: FiniteField> crate::fields::ConcurrentJob<F> for LiveJob<'_, N, F> {
    type Output = (Result<Preprocessed<N>, RowBudgetExceeded>, InternReport);
    fn run(self) -> Self::Output
    where
        F: Send + Sync,
    {
        symbolic_preprocessing_interned(
            self.basis,
            self.pairs,
            self.max_rows,
            self.selection,
            self.multiples,
            &self.config,
        )
    }
}

/// The live F4 hook: `Some` when [`with_live`] is in force on this thread, the batch is uncached
/// and the field can be shared across threads; `None` sends the caller down the shipping path.
pub(crate) fn live<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
    max_rows: usize,
    selection: ReducerSelection,
    multiples: PairMultiples,
    cached: bool,
) -> Option<Result<Preprocessed<N>, RowBudgetExceeded>> {
    let (config, mut total) = LIVE.get()?;
    if cached {
        return None;
    }
    let job = LiveJob {
        basis,
        pairs,
        max_rows,
        selection,
        multiples,
        config,
    };
    let (result, report) = F::run_concurrent(job).ok()?;
    accumulate(&mut total, &report);
    LIVE.set(Some((config, total)));
    Some(result)
}
