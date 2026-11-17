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
//! Either way a final per-slice pass writes `term_handles` from the translation arrays. At most
//! one worker team is spawned per batch, at the first step with at least `min_frontier`
//! monomials; narrower steps run on the caller alone, so a closure that never widens never starts
//! a team. Pair count does not predict closure size (an 11-pair Eco-12 batch needs 11 137 rows, a
//! 326-pair one 916), which is why the frontier starts the team and the seed does not.
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
    /// A batch with fewer seed rows takes the shipping serial closure; 0 disables the test. Kept
    /// to reproduce the first #860 campaign, which set 512 and lost most batches to it.
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
    /// Scratch buffers grown, all on the caller (#871).
    pub growths: usize,
    /// Slice scans repeated after a growth.
    pub rescans: usize,
    /// Scratch held after the batch, in bytes of capacity; maximized when summed.
    pub scratch_bytes: usize,
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
    /// One per term: a handle, or `LOCAL | id` into `candidates`; after emit, handles only.
    refs: Vec<u32>,
    /// Pre-step misses, deduplicated within the slice, in first-occurrence order.
    candidates: Vec<Keyed<N>>,
    /// Per shard, the candidate ids it holds, ascending. The sharded merge's only.
    by_shard: Vec<Vec<u32>>,
    local: Table<N>,
    counts: SymbolicCounts,
    /// Local id to handle, filled by the merge.
    translate: Vec<AtomicU32>,
    /// Whether this slice holds the step's first occurrence of the candidate.
    owner: Vec<AtomicBool>,
    /// Emit output: max over rows of (owners so far in the slice - frontier position).
    pending_peak: i64,
    /// Owners in local order, written by the sharded merge's ranking.
    new: Vec<Monomial<N>>,
    /// The scan finished this step.
    scanned: bool,
    /// The scan stopped short of a buffer this step.
    overflow: Option<Overflow>,
}

/// A buffer a slice's scan ran out of. Workers never grow scratch: a scan that would stops,
/// names the buffer, and the caller grows it and scans the slice again (#871).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Buffer {
    Refs,
    Candidates,
    ByShard(usize),
}

/// Where a slice's scan stopped: the buffer, and how many of the slice's items it had finished.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Overflow {
    buffer: Buffer,
    done: usize,
    total: usize,
}

impl<const N: usize> Slice<N> {
    fn bytes(&self) -> usize {
        use std::mem::size_of;
        self.rows.capacity() * size_of::<(usize, Monomial<N>, usize, usize)>()
            + self.refs.capacity() * 4
            + self.candidates.capacity() * size_of::<Keyed<N>>()
            + self.by_shard.iter().map(|v| v.capacity() * 4).sum::<usize>()
            + self.local.capacity() * (size_of::<(Keyed<N>, u32)>() + 1)
            + self.translate.capacity() * 4
            + self.owner.capacity()
            + self.new.capacity() * size_of::<Monomial<N>>()
    }

    /// Grow, on the calling thread, the buffer `overflow` names. The new capacity extrapolates
    /// from how far the scan got, so one more scan usually suffices.
    fn grow(&mut self, overflow: Overflow) {
        let want = |len: usize, cap: usize| {
            let projected = (len * overflow.total).div_ceil(overflow.done.max(1)) + len / 8;
            projected.max(2 * cap).max(64)
        };
        match overflow.buffer {
            Buffer::Refs => {
                let want = want(self.refs.len(), self.refs.capacity());
                self.refs.reserve_exact(want - self.refs.len());
            }
            Buffer::Candidates => {
                let want = want(self.candidates.len(), self.local.capacity());
                self.candidates.reserve_exact(want - self.candidates.len());
                self.local.reserve(want - self.local.len());
                // The scan's resizes of these must never outgrow them.
                let most = self.candidates.capacity().min(self.local.capacity());
                self.translate
                    .reserve_exact(most.saturating_sub(self.translate.len()));
                self.owner.reserve_exact(most.saturating_sub(self.owner.len()));
            }
            Buffer::ByShard(s) => {
                let v = &mut self.by_shard[s];
                let want = want(v.len(), v.capacity());
                v.reserve_exact(want - v.len());
            }
        }
    }
}

/// Step scratch owned by the caller and reused across steps and batches (#871).
///
/// glibc gives each thread its own arena and keeps what is freed there, so scratch a worker grows
/// stays resident after the batch where the caller's next allocations cannot reuse it: #860's
/// 1.20–1.31× peak RSS at 16 workers. Workers here write only within capacity the caller
/// allocated; a scan that needs more stops, and the caller grows the buffer and rescans the slice.
/// Kept from batch to batch, the scratch stops growing once the widest step has been seen.
#[derive(Default)]
pub struct InternScratch<const N: usize> {
    slices: Vec<RwLock<Slice<N>>>,
    growths: usize,
    rescans: usize,
}

impl<const N: usize> InternScratch<N> {
    /// Empty scratch; the first batches grow it.
    pub fn new() -> Self {
        Self::default()
    }

    /// Buffer growths so far, all made on the calling thread.
    pub fn growths(&self) -> usize {
        self.growths
    }

    /// Slice scans repeated after a growth.
    pub fn rescans(&self) -> usize {
        self.rescans
    }

    /// Scratch held, in bytes of capacity.
    pub fn bytes(&self) -> usize {
        self.slices.iter().map(|s| s.read().unwrap().bytes()).sum()
    }

    /// Each slice's buffer capacities.
    #[cfg(test)]
    pub(crate) fn capacities(&self) -> Vec<[usize; 7]> {
        self.slices
            .iter()
            .map(|s| {
                let s = s.read().unwrap();
                [
                    s.rows.capacity(),
                    s.refs.capacity(),
                    s.candidates.capacity(),
                    s.by_shard.iter().map(Vec::capacity).sum(),
                    s.local.capacity(),
                    s.translate.capacity(),
                    s.new.capacity(),
                ]
            })
            .collect()
    }
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
    /// The caller's scratch; a step uses the first `slice_count`.
    slices: &'a [RwLock<Slice<N>>],
    /// Whether scans fill `by_shard` (the sharded merge).
    route: bool,
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

/// Scan one slice: rows, their terms, pre-step lookups, local deduplication.
fn scan<const N: usize, F: FiniteField>(step: &Step<'_, N, F>, task: usize) {
    let mut slice = step.slices[task].write().unwrap();
    let slice = &mut *slice;
    if slice.scanned {
        return;
    }
    // One shard (the serial merge) needs no guard vector, so the common scan allocates nothing.
    let first = step.shards[0].read().unwrap();
    let rest: Vec<_> = step.shards[1..].iter().map(|s| s.read().unwrap()).collect();
    let shard_count = step.shards.len();
    let lookup = |key: &Keyed<N>| {
        let s = shard_of(key.hash, shard_count);
        let shard: &Shard<N> = if s == 0 { &first } else { &rest[s - 1] };
        shard.table.get(key).map(|&j| shard.handles[j as usize])
    };
    slice.rows.clear();
    slice.refs.clear();
    slice.candidates.clear();
    slice.local.clear();
    slice.by_shard.iter_mut().for_each(Vec::clear);
    slice.counts = SymbolicCounts::default();
    slice.overflow = None;
    let start = task * step.chunk;
    // Every write below stays within the capacity the caller gave; `Err` names the buffer that
    // would have had to grow.
    let push_terms =
        |slice: &mut Slice<N>, index: usize, multiplier: &Monomial<N>| -> Result<(), Buffer> {
            let length = step.basis.element(index).terms.len();
            if slice.refs.capacity() - slice.refs.len() < length {
                return Err(Buffer::Refs);
            }
            for (term, _) in step.basis.shifted_terms(index, multiplier) {
                let key = Keyed {
                    hash: BuildMonomialHasher.hash_one(term),
                    monomial: term,
                };
                let r = match lookup(&key) {
                    Some(handle) => handle,
                    None => {
                        let next = slice.candidates.len() as u32;
                        if slice.local.len() == slice.local.capacity()
                            || slice.candidates.len() == slice.candidates.capacity()
                        {
                            match slice.local.get(&key) {
                                Some(&id) => {
                                    slice.refs.push(LOCAL | id);
                                    continue;
                                }
                                None => return Err(Buffer::Candidates),
                            }
                        }
                        let id = *slice.local.entry(key).or_insert(next);
                        if id == next {
                            if step.route {
                                let s = shard_of(key.hash, shard_count);
                                let routed = &mut slice.by_shard[s];
                                if routed.len() == routed.capacity() {
                                    return Err(Buffer::ByShard(s));
                                }
                                routed.push(id);
                            }
                            slice.candidates.push(key);
                        }
                        LOCAL | id
                    }
                };
                slice.refs.push(r);
            }
            Ok(())
        };
    let seeds = step.frontier.is_empty();
    let end = (start + step.chunk).min(if seeds {
        step.seeds.len()
    } else {
        step.frontier.len()
    });
    let total = end.saturating_sub(start);
    for offset in 0..total {
        let position = start + offset + 1;
        let (index, multiplier) = if seeds {
            step.seeds[start + offset]
        } else {
            let monomial = &step.frontier[start + offset];
            if step.lcms.contains(monomial) {
                continue;
            }
            let Some(found) =
                step.basis
                    .find_divisor_with(monomial, step.selection, &mut slice.counts)
            else {
                continue;
            };
            found
        };
        if let Err(buffer) = push_terms(slice, index, &multiplier) {
            slice.overflow = Some(Overflow {
                buffer,
                done: offset,
                total,
            });
            return;
        }
        // The caller reserved a row per item.
        debug_assert!(slice.rows.len() < slice.rows.capacity());
        slice
            .rows
            .push((index, multiplier, position, slice.refs.len()));
    }
    let n = slice.candidates.len();
    // `grow` keeps these at least as long as `candidates` can be.
    slice.translate.clear();
    slice.translate.resize_with(n, || AtomicU32::new(0));
    slice.owner.clear();
    slice.owner.resize_with(n, || AtomicBool::new(false));
    slice.scanned = true;
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

/// Resolve slice `k`'s `refs` to handles in place — its run of `term_handles` — and its
/// contribution to the pending-queue peak.
fn emit<const N: usize, F: FiniteField>(step: &Step<'_, N, F>, k: usize) {
    let mut slice = step.slices[k].write().unwrap();
    let slice = &mut *slice;
    slice.pending_peak = i64::MIN;
    let (mut seen, mut owned, mut at) = (0u32, 0i64, 0usize);
    for &(_, _, position, end) in &slice.rows {
        for r in &mut slice.refs[at..end] {
            if *r & LOCAL != 0 {
                let id = *r & !LOCAL;
                if id == seen {
                    seen += 1;
                    owned += i64::from(slice.owner[id as usize].load(Relaxed));
                }
                *r = slice.translate[id as usize].load(Relaxed);
            }
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
    symbolic_preprocessing_interned_in(
        basis,
        pairs,
        max_rows,
        selection,
        multiples,
        config,
        &mut InternScratch::new(),
    )
}

/// [`symbolic_preprocessing_interned`] in the caller's `scratch`, which a run of batches shares
/// (#871).
///
/// # Panics
/// As [`symbolic_preprocessing_seeded`].
pub fn symbolic_preprocessing_interned_in<const N: usize, F: FiniteField + Sync>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
    max_rows: usize,
    selection: ReducerSelection,
    multiples: PairMultiples,
    config: &InternConfig,
    scratch: &mut InternScratch<N>,
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
    if scratch.slices.len() < slice_count {
        scratch.slices.resize_with(slice_count, RwLock::default);
    }
    let route = config.merge == Merge::Sharded;
    for slice in &mut scratch.slices[..slice_count] {
        let slice = slice.get_mut().unwrap();
        let wanted = if route { shard_count } else { 0 };
        if slice.by_shard.len() != wanted {
            slice.by_shard.resize_with(wanted, Vec::new);
        }
    }
    let (growths_before, rescans_before) = (scratch.growths, scratch.rescans);
    let InternScratch {
        slices: scratch_slices,
        growths,
        rescans,
    } = scratch;
    let step = RwLock::new(Step {
        basis,
        selection,
        lcms: &lcms,
        frontier: Vec::new(),
        seeds,
        chunk: 0,
        shards: (0..shard_count).map(|_| RwLock::default()).collect(),
        slices: &scratch_slices[..slice_count],
        route,
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
        // The team starts at the first step wide enough to dispatch, so a closure whose levels all
        // stay under `min_frontier` never pays for threads it would not use.
        let mut spawned = false;
        let mut spawn = |report: &mut InternReport| {
            if spawned {
                return;
            }
            spawned = true;
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
        };

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
                // A slice finds at most one row per item it scans.
                for slice in s.slices {
                    let mut slice = slice.write().unwrap();
                    slice.scanned = false;
                    if slice.rows.capacity() < s.chunk {
                        slice.rows.clear();
                        slice.rows.reserve_exact(s.chunk);
                        *growths += 1;
                    }
                }
            }
            report.steps += 1;
            report.dispatched_steps += usize::from(dispatched);
            if dispatched {
                spawn(&mut report);
            }

            run(Job::Scan, dispatched, &mut report.scan);
            // Grow on this thread whatever a scan ran out of, and scan those slices again.
            loop {
                let mut short = 0;
                for slice in step.read().unwrap().slices {
                    let mut slice = slice.write().unwrap();
                    if let Some(overflow) = slice.overflow.take() {
                        slice.grow(overflow);
                        short += 1;
                    }
                }
                if short == 0 {
                    break;
                }
                *growths += short;
                *rescans += short;
                run(Job::Scan, dispatched, &mut report.scan);
            }

            // Merge.
            let merging = Instant::now();
            match config.merge {
                Merge::Serial => {
                    let s = step.read().unwrap();
                    let mut shard = s.shards[0].write().unwrap();
                    let shard = &mut *shard;
                    for slice in s.slices {
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
                        for slice in s.slices {
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
                        // Ranking writes a slice's owners to `new`; at most its candidates.
                        for slice in s.slices {
                            let mut slice = slice.write().unwrap();
                            if slice.new.capacity() < slice.candidates.len() {
                                let wanted = slice.candidates.len();
                                slice.new.clear();
                                slice.new.reserve_exact(wanted);
                                *growths += 1;
                            }
                        }
                    }
                    run(Job::Rank, dispatched, &mut clock);
                    run(Job::Record, dispatched, &mut clock);
                    report.merge += merging.elapsed();
                    let stitching = Instant::now();
                    let s = step.read().unwrap();
                    for slice in s.slices {
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
            // One amortized growth per step rather than one per slice.
            let (step_terms, step_rows) = s.slices.iter().fold((0, 0), |(t, r), slice| {
                let slice = slice.read().unwrap();
                (t + slice.refs.len(), r + slice.rows.len())
            });
            term_handles.reserve(step_terms);
            if !seed_step {
                rows.reserve(step_rows);
                leads.reserve(step_rows);
            }
            let mut admitted_before = 0i64;
            let mut peak = if seed_step {
                0
            } else {
                counts.max_pending_monomials as i64
            };
            for slice in s.slices {
                let slice = slice.read().unwrap();
                counts.add(&slice.counts);
                counts.monomials_enqueued += slice.refs.len();
                term_handles.extend_from_slice(&slice.refs);
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
        if report.dispatched_steps > 0 {
            team.barrier.as_ref().unwrap().wait();
        }
    });
    drop(step);
    report.growths = *growths - growths_before;
    report.rescans = *rescans - rescans_before;
    report.scratch_bytes = scratch_slices
        .iter()
        .map(|s| s.read().unwrap().bytes())
        .sum();

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

type AnyScratch = Option<Box<dyn std::any::Any>>;

thread_local! {
    static LIVE: std::cell::Cell<Option<(InternConfig, InternReport)>> =
        const { std::cell::Cell::new(None) };
    /// The run's [`InternScratch`], typed by the batches' `N`.
    static SCRATCH: std::cell::RefCell<AnyScratch> = const { std::cell::RefCell::new(None) };
}

/// Run `f` with live F4 on this thread taking [`symbolic_preprocessing_interned`] under `config`,
/// and return the reports of every batch it served, summed. The batches share one
/// [`InternScratch`], freed when `f` returns.
pub fn with_live<R>(config: InternConfig, f: impl FnOnce() -> R) -> (R, InternReport) {
    struct Reset(Option<(InternConfig, InternReport)>, AnyScratch);
    impl Drop for Reset {
        fn drop(&mut self) {
            LIVE.set(self.0);
            SCRATCH.set(self.1.take());
        }
    }
    let reset = Reset(
        LIVE.replace(Some((config, InternReport::default()))),
        SCRATCH.take(),
    );
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
    total.growths += batch.growths;
    total.rescans += batch.rescans;
    total.scratch_bytes = total.scratch_bytes.max(batch.scratch_bytes);
}

struct LiveJob<'a, const N: usize, F: FiniteField> {
    basis: &'a MonicBasis<N, F>,
    pairs: &'a [CriticalPair<N>],
    max_rows: usize,
    selection: ReducerSelection,
    multiples: PairMultiples,
    config: InternConfig,
    scratch: &'a mut InternScratch<N>,
}

impl<const N: usize, F: FiniteField> crate::fields::ConcurrentJob<F> for LiveJob<'_, N, F> {
    type Output = (Result<Preprocessed<N>, RowBudgetExceeded>, InternReport);
    fn run(self) -> Self::Output
    where
        F: Send + Sync,
    {
        symbolic_preprocessing_interned_in(
            self.basis,
            self.pairs,
            self.max_rows,
            self.selection,
            self.multiples,
            &self.config,
            self.scratch,
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
    let mut scratch = SCRATCH
        .take()
        .and_then(|any| any.downcast::<InternScratch<N>>().ok())
        .unwrap_or_default();
    let job = LiveJob {
        basis,
        pairs,
        max_rows,
        selection,
        multiples,
        config,
        scratch: &mut scratch,
    };
    let outcome = F::run_concurrent(job).ok();
    SCRATCH.set(Some(scratch));
    let (result, report) = outcome?;
    accumulate(&mut total, &report);
    LIVE.set(Some((config, total)));
    Some(result)
}
