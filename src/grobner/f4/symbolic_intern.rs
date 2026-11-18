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
//! Step scratch is the caller's ([`InternScratch`], #871): workers write only within capacity the
//! caller allocated, so nothing they touch lands in a glibc per-thread arena, and the scratch is
//! sized to what a step touches (16-byte candidates, 8-byte index slots) because the symbolic
//! stage, not the matrix, is where a wide batch peaks.
//!
//! Matrix construction sorts columns by monomial and reducer rows by leading column, so only the
//! *set* of reducer rows and the pair rows' order reach the matrix; exact handle identity is kept
//! here so the result can be compared with `==`, not because the matrix needs it.
//!
//! #861 ships the serial merge behind `F4Options::parallel_symbolic`, with steps below
//! `min_frontier` interned straight into the columns on the caller (no candidates, no scratch).
//! The sharded merge and the replay entry points remain `research-work` instruments.
#![cfg_attr(not(feature = "research-work"), allow(dead_code))]
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
    /// How long the step scratch outlives a batch (#871).
    pub retain: Retain,
}

/// What bounds a parallel closure besides its row budget (#872).
pub struct Limits<'a> {
    /// Live entries the step scratch may be charged, as
    /// [`F4Options::live_entry_allowance`](super::F4Options::live_entry_allowance).
    pub entry_allowance: usize,
    /// Bytes one live entry stands for, as
    /// [`F4Options::bytes_per_entry`](super::F4Options::bytes_per_entry).
    pub bytes_per_entry: usize,
    /// Consulted at every step boundary; true returns [`Refusal::Stopped`].
    pub stop: &'a dyn Fn() -> bool,
}

impl Limits<'_> {
    /// No allowance and no stop.
    pub fn none() -> Limits<'static> {
        Limits {
            entry_allowance: usize::MAX,
            bytes_per_entry: 16,
            stop: &|| false,
        }
    }

    /// `bytes` of scratch as live entries, rounded up.
    fn entries(&self, bytes: usize) -> usize {
        bytes.div_ceil(self.bytes_per_entry.max(1))
    }
}

/// Why a parallel closure returned without a result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Refusal {
    /// The row budget, refused exactly where the serial closure refuses.
    Rows(RowBudgetExceeded),
    /// The step scratch would hold more than [`Limits::entry_allowance`], charged by capacity.
    LiveEntries {
        /// The charge that crossed the allowance.
        entries: usize,
    },
    /// [`Limits::stop`] asked for it at a step boundary.
    Stopped,
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
    /// Of the step phases above, the seed step's: interning the seed rows' terms (#888).
    pub seed_step: Duration,
    /// Of [`Self::scan`], the steps the caller ran alone, interning as it scanned (#888).
    pub solo: Duration,
    /// Scratch buffers grown, all on the caller (#871).
    pub growths: usize,
    /// Slice scans repeated after a growth.
    pub rescans: usize,
    /// Scratch held after the batch, in bytes of capacity; maximized when summed.
    pub scratch_bytes: usize,
    /// The largest live-entry charge the step scratch made (#872); maximized when summed.
    pub charged_entries: usize,
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
    candidates: Vec<Candidate>,
    /// Per shard, the candidate ids it holds, ascending. The sharded merge's only.
    by_shard: Vec<Vec<u32>>,
    local: LocalIndex,
    counts: SymbolicCounts,
    /// Local id to handle, filled by the merge.
    translate: Vec<AtomicU32>,
    /// Whether this slice holds the step's first occurrence of the candidate.
    owner: Vec<AtomicBool>,
    /// Emit output: max over rows of (owners so far in the slice - frontier position).
    pending_peak: i64,
    /// Owners this step: the monomials the merge admitted from this slice.
    admitted: usize,
    /// Owners in local order, written by the sharded merge's ranking.
    new: Vec<Monomial<N>>,
    /// The scan finished this step.
    scanned: bool,
    /// The scan stopped short of a buffer this step.
    overflow: Option<Overflow>,
    /// Allocated to its hint for this batch: only a prepared slice's capacities are remembered.
    hinted: bool,
}

/// A pre-step miss, named by where the slice first met it — row and term — rather than by its
/// monomial: 16 bytes instead of 8 plus a monomial (56 at twelve variables), and the candidate
/// list is most of the scratch.
#[derive(Clone, Copy, Debug)]
struct Candidate {
    hash: u64,
    row: u32,
    term: u32,
}

/// The monomial `candidate` stands for: term `term` of row `row`'s shifted basis element.
fn candidate_monomial<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    rows: &[(usize, Monomial<N>, usize, usize)],
    candidate: &Candidate,
) -> Monomial<N> {
    let (index, multiplier, _, _) = &rows[candidate.row as usize];
    &basis.element(*index).terms[candidate.term as usize].0 * multiplier
}

/// `candidate` with its monomial, for the interner.
fn candidate_key<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    rows: &[(usize, Monomial<N>, usize, usize)],
    candidate: &Candidate,
) -> Keyed<N> {
    Keyed {
        hash: candidate.hash,
        monomial: candidate_monomial(basis, rows, candidate),
    }
}

/// A slice's deduplication table: open addressing over candidate ids, 8 bytes a slot.
///
/// A hash table's inserts land all over its bucket array, so every page of it is resident however
/// few entries it holds. A table kept at the run's widest step would be resident at that size in
/// every step: 63 MiB of `HashMap<Keyed, u32>` on Eco-12 at 16 workers. This one holds ids only
/// (the keys are in `candidates`), starts every step small, and doubles in place within the
/// capacity the caller reserved, so only the slots a step needs are ever touched.
#[derive(Default)]
struct LocalIndex {
    /// `tag << 32 | (id + 1)`, the tag being the hash's top 32 bits; 0 is empty. The length in
    /// use is a power of two at least twice the entries.
    slots: Vec<u64>,
    len: usize,
}

impl LocalIndex {
    const FIRST: usize = 256;

    /// Slots ever usable without the caller growing the table.
    fn capacity(&self) -> usize {
        self.slots.capacity()
    }

    /// Entries the table can take before it needs [`Self::capacity`] to grow.
    fn room(&self) -> usize {
        prev_power_of_two(self.slots.capacity()) / 2
    }

    fn clear(&mut self) {
        self.len = 0;
        self.slots.clear();
        let first = Self::FIRST.min(prev_power_of_two(self.slots.capacity()));
        self.slots.resize(first, 0);
    }

    /// The id of the entry with `hash` for which `is` holds, or `None` after inserting one as id
    /// `len`, the entries so far, whose hashes `hash_of` gives; `Err` when the table would have
    /// to outgrow its capacity.
    fn find_or_insert(
        &mut self,
        hash: u64,
        is: impl Fn(u32) -> bool,
        hash_of: impl Fn(usize) -> u64,
        len: usize,
    ) -> Result<Option<u32>, ()> {
        debug_assert_eq!(len, self.len);
        if self.slots.is_empty() {
            return Err(());
        }
        let tag = hash >> 32;
        let mut mask = self.slots.len() - 1;
        let mut i = hash as usize & mask;
        loop {
            let slot = self.slots[i];
            if slot == 0 {
                break;
            }
            let id = (slot as u32) - 1;
            if slot >> 32 == tag && is(id) {
                return Ok(Some(id));
            }
            i = (i + 1) & mask;
        }
        if 2 * (len + 1) > self.slots.len() {
            let doubled = 2 * self.slots.len();
            if doubled > self.slots.capacity() {
                return Err(());
            }
            self.slots.clear();
            self.slots.resize(doubled, 0);
            mask = doubled - 1;
            for id in 0..len {
                self.place(hash_of(id), id, mask);
            }
            self.place(hash, len, mask);
        } else {
            self.slots[i] = tag << 32 | (len as u64 + 1);
        }
        self.len += 1;
        Ok(None)
    }

    /// The id of the entry with `hash` for which `is` holds.
    fn find(&self, hash: u64, is: impl Fn(u32) -> bool) -> Option<u32> {
        if self.slots.is_empty() {
            return None;
        }
        let (tag, mask) = (hash >> 32, self.slots.len() - 1);
        let mut i = hash as usize & mask;
        loop {
            let slot = self.slots[i];
            if slot == 0 {
                return None;
            }
            let id = (slot as u32) - 1;
            if slot >> 32 == tag && is(id) {
                return Some(id);
            }
            i = (i + 1) & mask;
        }
    }

    /// [`Self::find_or_insert`], growing the capacity when it must: for the caller's own table.
    fn find_or_insert_growing(
        &mut self,
        hash: u64,
        is: impl Fn(u32) -> bool,
        hash_of: impl Fn(usize) -> u64,
        len: usize,
    ) -> Option<u32> {
        if self.slots.is_empty() {
            self.slots.reserve_exact(Self::FIRST);
            self.slots.resize(Self::FIRST, 0);
        }
        if 2 * (len + 1) > self.slots.len() && 2 * self.slots.len() > self.slots.capacity() {
            self.slots
                .reserve_exact(2 * self.slots.len() - self.slots.len());
        }
        self.find_or_insert(hash, is, hash_of, len)
            .expect("capacity reserved above")
    }

    fn place(&mut self, hash: u64, id: usize, mask: usize) {
        let mut i = hash as usize & mask;
        while self.slots[i] != 0 {
            i = (i + 1) & mask;
        }
        self.slots[i] = (hash >> 32) << 32 | (id as u64 + 1);
    }
}

fn prev_power_of_two(n: usize) -> usize {
    if n == 0 {
        0
    } else {
        1 << (usize::BITS - 1 - n.leading_zeros())
    }
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
            + self.candidates.capacity() * size_of::<Candidate>()
            + self
                .by_shard
                .iter()
                .map(|v| v.capacity() * 4)
                .sum::<usize>()
            + self.local.capacity() * 8
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
                let want = want(self.candidates.len(), self.candidates.capacity());
                self.candidates.reserve_exact(want - self.candidates.len());
                let slots = (2 * want).next_power_of_two();
                let slots_now = self.local.slots.len();
                self.local.slots.reserve_exact(slots - slots_now);
                // The scan's resizes of these must never outgrow them.
                let most = self.candidates.capacity().min(self.local.room());
                self.translate
                    .reserve_exact(most.saturating_sub(self.translate.len()));
                self.owner
                    .reserve_exact(most.saturating_sub(self.owner.len()));
            }
            Buffer::ByShard(s) => {
                let v = &mut self.by_shard[s];
                let want = want(v.len(), v.capacity());
                v.reserve_exact(want - v.len());
            }
        }
    }
}

/// A slice's buffer capacities, carried from one batch to the next when the buffers are not.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Hint {
    rows: usize,
    refs: usize,
    candidates: usize,
    local: usize,
    by_shard: Vec<usize>,
    new: usize,
}

impl<const N: usize> Slice<N> {
    fn hint(&self) -> Hint {
        Hint {
            rows: self.rows.capacity(),
            refs: self.refs.capacity(),
            candidates: self.candidates.capacity(),
            local: self.local.capacity(),
            by_shard: self.by_shard.iter().map(Vec::capacity).collect(),
            new: self.new.capacity(),
        }
    }

    /// Fresh buffers of the hinted capacities, allocated on the calling thread.
    fn hinted(hint: &Hint) -> Self {
        let most = hint.candidates.min(prev_power_of_two(hint.local) / 2);
        Self {
            rows: Vec::with_capacity(hint.rows),
            refs: Vec::with_capacity(hint.refs),
            candidates: Vec::with_capacity(hint.candidates),
            by_shard: hint
                .by_shard
                .iter()
                .map(|&c| Vec::with_capacity(c))
                .collect(),
            local: LocalIndex {
                slots: Vec::with_capacity(hint.local),
                len: 0,
            },
            translate: Vec::with_capacity(most),
            owner: Vec::with_capacity(most),
            new: Vec::with_capacity(hint.new),
            hinted: true,
            ..Self::default()
        }
    }
}

/// How long [`InternScratch`] keeps its buffers.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Retain {
    /// Free the buffers after each batch and keep only their capacities, which the next batch
    /// allocates up front. Freed on the caller, the memory is reused by the batch's matrix.
    #[default]
    Batch,
    /// Keep the buffers for the whole run: no allocation at all after warm-up, but the scratch
    /// is resident through every matrix, on top of the shipping peak.
    Run,
}

/// Step scratch owned by the caller and reused across steps and batches (#871).
///
/// glibc gives each thread its own arena and keeps what is freed there, so scratch a worker grows
/// stays resident after the batch where the caller's next allocations cannot reuse it: #860's
/// 1.20–1.31× peak RSS at 16 workers. Workers here write only within capacity the caller
/// allocated; a scan that needs more stops, and the caller grows the buffer and rescans the slice.
/// Capacities persist from batch to batch under either [`Retain`], so growth and rescans stop
/// once the widest step has been seen.
#[derive(Default)]
pub struct InternScratch<const N: usize> {
    slices: Vec<RwLock<Slice<N>>>,
    hints: Vec<Hint>,
    growths: usize,
    rescans: usize,
}

impl<const N: usize> InternScratch<N> {
    /// Empty scratch; the first batches size it.
    pub fn new() -> Self {
        Self::default()
    }

    /// Before a batch: `count` slices, allocated to the hinted capacities where they were freed.
    fn open(&mut self, count: usize) {
        if self.slices.len() < count {
            self.slices.resize_with(count, RwLock::default);
        }
    }

    /// After a batch: remember every slice's capacities, and free the buffers unless kept.
    fn close(&mut self, retain: Retain) {
        let hints: Vec<Hint> = self
            .slices
            .iter()
            .enumerate()
            .map(|(k, s)| {
                let s = s.read().unwrap();
                if s.hinted {
                    s.hint()
                } else {
                    self.hints.get(k).cloned().unwrap_or_default()
                }
            })
            .collect();
        if hints.len() >= self.hints.len() {
            self.hints = hints;
        } else {
            self.hints[..hints.len()].clone_from_slice(&hints);
        }
        if retain == Retain::Batch {
            self.slices = Vec::new();
        }
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

    /// Each slice's buffer capacities as of the last batch.
    #[cfg(test)]
    pub(crate) fn capacities(&self) -> Vec<impl Eq + std::fmt::Debug> {
        self.hints.clone()
    }

    /// Whether buffers are held between batches.
    #[cfg(test)]
    pub(crate) fn holds_buffers(&self) -> bool {
        !self.slices.is_empty()
    }
}

/// One shard of the interner: monomial to an index into `handles`.
#[derive(Default)]
struct Shard<const N: usize> {
    /// The sharded merge's: monomial to an index into `handles`.
    table: Table<N>,
    /// The serial merge's: handles into `Step::monomials`, 8 bytes a slot where `table` takes
    /// a monomial, its hash and an index, which is what kept MQ10 over budget.
    index: LocalIndex,
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
    /// The columns so far, in handle order; the serial merge appends, between phases.
    monomials: Vec<Monomial<N>>,
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
        if !step.route {
            return first
                .index
                .find(key.hash, |h| step.monomials[h as usize] == key.monomial);
        }
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
    // The row is pushed before its terms, so a candidate can name the row it was first met in.
    let push_terms =
        |slice: &mut Slice<N>, index: usize, multiplier: &Monomial<N>| -> Result<(), Buffer> {
            let length = step.basis.element(index).terms.len();
            if slice.refs.capacity() - slice.refs.len() < length {
                return Err(Buffer::Refs);
            }
            let row = (slice.rows.len() - 1) as u32;
            for (t, (term, _)) in step.basis.shifted_terms(index, multiplier).enumerate() {
                let key = Keyed {
                    hash: BuildMonomialHasher.hash_one(term),
                    monomial: term,
                };
                let r = match lookup(&key) {
                    Some(handle) => handle,
                    None => {
                        // Room for one more candidate is checked before the lookup, which may
                        // insert; a full buffer stops the scan a little early, never wrongly.
                        if slice.candidates.len() == slice.candidates.capacity() {
                            return Err(Buffer::Candidates);
                        }
                        let s = shard_of(key.hash, shard_count);
                        if step.route && slice.by_shard[s].len() == slice.by_shard[s].capacity() {
                            return Err(Buffer::ByShard(s));
                        }
                        let (candidates, rows) = (&slice.candidates, &slice.rows);
                        let is = |id: u32| {
                            candidate_monomial(step.basis, rows, &candidates[id as usize])
                                == key.monomial
                        };
                        match slice.local.find_or_insert(
                            key.hash,
                            is,
                            |id| candidates[id].hash,
                            candidates.len(),
                        ) {
                            Ok(Some(id)) => LOCAL | id,
                            Ok(None) => {
                                let id = slice.candidates.len() as u32;
                                if step.route {
                                    slice.by_shard[s].push(id);
                                }
                                slice.candidates.push(Candidate {
                                    hash: key.hash,
                                    row,
                                    term: t as u32,
                                });
                                LOCAL | id
                            }
                            Err(()) => return Err(Buffer::Candidates),
                        }
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
        // The caller reserved a row per item.
        debug_assert!(slice.rows.len() < slice.rows.capacity());
        slice.rows.push((index, multiplier, position, 0));
        if let Err(buffer) = push_terms(slice, index, &multiplier) {
            slice.overflow = Some(Overflow {
                buffer,
                done: offset,
                total,
            });
            return;
        }
        let end = slice.refs.len();
        slice.rows.last_mut().expect("pushed above").3 = end;
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
            let key = candidate_key(step.basis, &slice.rows, &slice.candidates[id as usize]);
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
            let monomial = candidate_monomial(step.basis, &slice.rows, &slice.candidates[id]);
            slice.new.push(monomial);
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

/// A step below `min_frontier`, on the caller alone (#861): every term is interned straight into
/// the columns in scan order, which is the serial closure's first-occurrence order, so there are
/// no candidates, no merge and no emit, and no scratch is touched. Returns the step's
/// pending-queue contribution as emit computes it for one slice: the largest count of monomials
/// admitted so far less the frontier position, over the rows found; `None` without rows.
fn solo_step<const N: usize, F: FiniteField>(
    step: &mut Step<'_, N, F>,
    seed_step: bool,
    monomials: &mut Vec<Monomial<N>>,
    rows: &mut Vec<PreprocessedRow<N>>,
    leads: &mut MonomialSet<N>,
    term_handles: &mut Vec<MonomialHandle>,
    counts: &mut SymbolicCounts,
) -> Option<i64> {
    let Step {
        basis,
        selection,
        lcms,
        frontier,
        seeds,
        shards,
        ..
    } = step;
    let index = &mut shards[0].get_mut().unwrap().index;
    let width = if seed_step {
        seeds.len()
    } else {
        frontier.len()
    };
    let mut found = SymbolicCounts::default();
    let (mut peak, mut admitted) = (None, 0i64);
    for offset in 0..width {
        let (basis_index, multiplier) = if seed_step {
            seeds[offset]
        } else {
            let monomial = &frontier[offset];
            if lcms.contains(monomial) {
                continue;
            }
            let Some(divisor) = basis.find_divisor_with(monomial, *selection, &mut found) else {
                continue;
            };
            divisor
        };
        for (term, _) in basis.shifted_terms(basis_index, &multiplier) {
            let hash = BuildMonomialHasher.hash_one(term);
            let arena = &*monomials;
            let known = index.find_or_insert_growing(
                hash,
                |h| arena[h as usize] == term,
                |h| BuildMonomialHasher.hash_one(arena[h]),
                arena.len(),
            );
            let handle = known.unwrap_or_else(|| {
                let handle = MonomialHandle::try_from(monomials.len())
                    .ok()
                    .filter(|h| h & LOCAL == 0)
                    .expect("fewer distinct monomials than a handle can name");
                monomials.push(term);
                admitted += 1;
                handle
            });
            term_handles.push(handle);
            found.monomials_enqueued += 1;
        }
        if !seed_step {
            leads.insert(frontier[offset]);
            rows.push(PreprocessedRow {
                multiplier,
                basis_index,
                kind: RowKind::Reducer,
            });
            let here = admitted - (offset as i64 + 1);
            peak = Some(peak.map_or(here, |p: i64| p.max(here)));
        }
    }
    counts.add(&found);
    peak
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
    let (result, report) = symbolic_preprocessing_interned_in(
        basis,
        pairs,
        max_rows,
        selection,
        multiples,
        config,
        &mut InternScratch::new(),
        &Limits::none(),
    );
    let result = result.map_err(|refusal| match refusal {
        Refusal::Rows(exceeded) => exceeded,
        Refusal::LiveEntries { .. } | Refusal::Stopped => unreachable!("no limits were set"),
    });
    (result, report)
}

/// [`symbolic_preprocessing_interned`] in the caller's `scratch`, which a run of batches shares
/// (#871), under `limits` (#872).
///
/// The scratch is charged to `limits.entry_allowance` by capacity whenever it is allocated or
/// grown, for the duration of the call; the caller frees or keeps it per [`Retain`], and nothing
/// is charged once the call returns. A batch whose scratch would exceed the allowance is refused
/// before the step that needs it runs. `limits.stop` is consulted before every step, the
/// granularity at which a closure can stop without a partial result to undo.
///
/// # Panics
/// As [`symbolic_preprocessing_seeded`].
#[allow(clippy::too_many_arguments)]
pub fn symbolic_preprocessing_interned_in<const N: usize, F: FiniteField + Sync>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
    max_rows: usize,
    selection: ReducerSelection,
    multiples: PairMultiples,
    config: &InternConfig,
    scratch: &mut InternScratch<N>,
    limits: &Limits<'_>,
) -> (Result<Preprocessed<N>, Refusal>, InternReport) {
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
        return (result.map_err(Refusal::Rows), report);
    }
    if rows.len() > max_rows {
        return (
            Err(Refusal::Rows(RowBudgetExceeded { limit: max_rows })),
            report,
        );
    }

    let workers = config.workers;
    let slice_count = workers * config.slices_per_worker.max(1);
    let shard_count = match config.merge {
        Merge::Serial => 1,
        Merge::Sharded => workers,
    };
    let seeds: Vec<(usize, Monomial<N>)> =
        rows.iter().map(|r| (r.basis_index, r.multiplier)).collect();
    scratch.open(slice_count);
    let route = config.merge == Merge::Sharded;
    let (growths_before, rescans_before) = (scratch.growths, scratch.rescans);
    let InternScratch {
        slices: scratch_slices,
        growths,
        rescans,
        hints,
    } = &mut *scratch;
    let hints: &[Hint] = hints;
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
        monomials: Vec::new(),
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
    let mut refused: Option<Refusal> = None;

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
        let charge = |slices: &[RwLock<Slice<N>>]| {
            limits.entries(slices.iter().map(|s| s.read().unwrap().bytes()).sum())
        };
        let mut prepared = false;
        'steps: loop {
            let level_start = monomials.len();
            let (step_started, seeding) = (Instant::now(), seed_step);
            let dispatched;
            let solo;
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
                // A step boundary: nothing of this step has run, so stopping leaves nothing to
                // undo (#872).
                if (limits.stop)() {
                    refused = Some(Refusal::Stopped);
                    break;
                }
                dispatched = size >= config.min_frontier;
                solo = !dispatched && config.merge == Merge::Serial;
                if !solo {
                    // The slices take their hinted capacities only once a step needs them, so a
                    // batch whose steps all run solo allocates no scratch at all (#861).
                    if !prepared {
                        prepared = true;
                        let wanted = if route { shard_count } else { 0 };
                        for (k, slice) in s.slices.iter().enumerate() {
                            let mut slice = slice.write().unwrap();
                            if !slice.hinted {
                                *slice = Slice::hinted(hints.get(k).unwrap_or(&Hint::default()));
                            }
                            if slice.by_shard.len() != wanted {
                                slice.by_shard.resize_with(wanted, Vec::new);
                            }
                        }
                    }
                    s.chunk = size.div_ceil(if dispatched { slice_count } else { 1 });
                    // Scans read the columns so far; the caller has them back before the merge.
                    s.monomials = std::mem::take(&mut monomials);
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
                    // Charged before the scan, so a step whose scratch would not fit never runs.
                    let entries = charge(s.slices);
                    report.charged_entries = report.charged_entries.max(entries);
                    if entries > limits.entry_allowance {
                        refused = Some(Refusal::LiveEntries { entries });
                        break;
                    }
                }
            }
            report.steps += 1;
            report.dispatched_steps += usize::from(dispatched);
            if solo {
                let started = Instant::now();
                let mut s = step.write().unwrap();
                let s = &mut *s;
                let width = if seed_step {
                    s.seeds.len()
                } else {
                    s.frontier.len()
                } as i64;
                let peak = solo_step(
                    s,
                    seed_step,
                    &mut monomials,
                    &mut rows,
                    &mut leads,
                    &mut term_handles,
                    &mut counts,
                );
                let admitted = monomials.len() - level_start;
                report.candidates += admitted;
                report.owners += admitted;
                if seed_step {
                    counts.max_pending_monomials = admitted;
                    seed_step = false;
                } else if let Some(peak) = peak {
                    counts.max_pending_monomials =
                        counts.max_pending_monomials.max((width + peak) as usize);
                }
                s.frontier.clear();
                s.frontier.extend_from_slice(&monomials[level_start..]);
                let solo_time = started.elapsed();
                report.scan += solo_time;
                report.solo += solo_time;
                if seeding {
                    report.seed_step += step_started.elapsed();
                }
                if rows.len() > max_rows {
                    refused = Some(Refusal::Rows(RowBudgetExceeded { limit: max_rows }));
                    break;
                }
                continue;
            }
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
                let entries = charge(step.read().unwrap().slices);
                report.charged_entries = report.charged_entries.max(entries);
                if entries > limits.entry_allowance {
                    refused = Some(Refusal::LiveEntries { entries });
                    break 'steps;
                }
                run(Job::Scan, dispatched, &mut report.scan);
            }
            monomials = std::mem::take(&mut step.write().unwrap().monomials);

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
                        let before = monomials.len();
                        for (id, candidate) in slice.candidates.iter().enumerate() {
                            let monomial = candidate_monomial(basis, &slice.rows, candidate);
                            let arena = &monomials;
                            let found = shard.index.find_or_insert_growing(
                                candidate.hash,
                                |h| arena[h as usize] == monomial,
                                |h| BuildMonomialHasher.hash_one(arena[h]),
                                arena.len(),
                            );
                            if let Some(handle) = found {
                                slice.owner[id].store(false, Relaxed);
                                slice.translate[id].store(handle, Relaxed);
                            } else {
                                let handle = MonomialHandle::try_from(monomials.len())
                                    .ok()
                                    .filter(|h| h & LOCAL == 0)
                                    .expect("fewer distinct monomials than a handle can name");
                                slice.owner[id].store(true, Relaxed);
                                slice.translate[id].store(handle, Relaxed);
                                monomials.push(monomial);
                            }
                        }
                        slice.admitted = monomials.len() - before;
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
                        let mut slice = slice.write().unwrap();
                        slice.admitted = slice.new.len();
                        monomials.extend_from_slice(&slice.new);
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
                admitted_before += slice.admitted as i64;
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
            if seeding {
                report.seed_step += step_started.elapsed();
            }
            if rows.len() > max_rows {
                refused = Some(Refusal::Rows(RowBudgetExceeded { limit: max_rows }));
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
    scratch.close(config.retain);

    if let Some(refusal) = refused {
        return (Err(refusal), report);
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

#[cfg(feature = "research-work")]
thread_local! {
    static LIVE: std::cell::Cell<Option<(InternConfig, InternReport)>> =
        const { std::cell::Cell::new(None) };
}

/// Run `f` with live F4 on this thread taking [`symbolic_preprocessing_interned`] under `config`,
/// whatever [`F4Options::parallel_symbolic`](super::F4Options::parallel_symbolic) says, and return
/// the reports of every batch it served, summed. Each F4 run's batches share one
/// [`InternScratch`], freed when the run returns.
#[cfg(feature = "research-work")]
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

#[cfg(feature = "research-work")]
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
    total.seed_step += batch.seed_step;
    total.solo += batch.solo;
    total.growths += batch.growths;
    total.rescans += batch.rescans;
    total.scratch_bytes = total.scratch_bytes.max(batch.scratch_bytes);
    total.charged_entries = total.charged_entries.max(batch.charged_entries);
}

struct LiveJob<'a, const N: usize, F: FiniteField> {
    basis: &'a MonicBasis<N, F>,
    pairs: &'a [CriticalPair<N>],
    max_rows: usize,
    selection: ReducerSelection,
    multiples: PairMultiples,
    config: InternConfig,
    scratch: &'a mut InternScratch<N>,
    limits: Limits<'a>,
}

impl<const N: usize, F: FiniteField> crate::fields::ConcurrentJob<F> for LiveJob<'_, N, F> {
    type Output = (Result<Preprocessed<N>, Refusal>, InternReport);
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
            &self.limits,
        )
    }
}

thread_local! {
    /// The running F4 call's wall clock and budget, once its time check is armed (#872).
    static DEADLINE: std::cell::Cell<Option<(Instant, Duration)>> =
        const { std::cell::Cell::new(None) };
}

/// Called by the F4 batch loop where it checks [`F4Options::max_wall_time`]: `Some` once a batch
/// has been reduced, which is when the loop's own check starts to apply, so the parallel closure
/// honors the budget under the same rule; `None` before that.
///
/// [`F4Options::max_wall_time`]: super::F4Options::max_wall_time
pub(crate) fn arm_deadline(armed: Option<(Instant, Duration)>) {
    DEADLINE.set(armed);
}

/// The configuration `options` asks for, or `None` for the serial closure (#861).
pub(crate) fn configured(options: &super::F4Options) -> Option<InternConfig> {
    use super::ParallelSymbolic;
    let workers = options.parallel_symbolic.workers();
    (workers > 1).then_some(InternConfig {
        workers,
        merge: Merge::Serial,
        min_frontier: ParallelSymbolic::min_frontier(workers),
        slices_per_worker: ParallelSymbolic::SLICES_PER_WORKER,
        min_seed_rows: 0,
        retain: Retain::Batch,
    })
}

/// The live F4 hook: `Some` when [`F4Options::parallel_symbolic`] (or, under `research-work`, a
/// [`with_live`] override on this thread) asks for a team, the batch is uncached and the field can
/// be shared across threads; `None` sends the caller down the serial closure.
///
/// Beyond the row budget the closure is held to `options`' live-entry allowance, its scratch
/// charged as entries of `F`: a batch whose scratch would not fit takes the serial closure (a
/// research override refuses it instead). It is stopped at a step boundary by `observer_stop` (as
/// [`F4Error::StoppedByObserver`]) or by the armed wall-time budget (as
/// [`F4Error::TimeBudgetExceeded`]).
///
/// [`F4Options::parallel_symbolic`]: super::F4Options::parallel_symbolic
pub(crate) fn live<const N: usize, F: FiniteField>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
    options: &super::F4Options,
    cache: &mut ReducerCache<N>,
    observer_stop: &dyn Fn() -> bool,
) -> Option<Result<Preprocessed<N>, super::F4Error>> {
    use super::{symbolic::CacheMode, F4Error, F4Options};
    #[cfg(feature = "research-work")]
    let research = LIVE.get();
    // A `live_symbolic` research policy modifies the serial closure, so it keeps the batch there.
    #[cfg(feature = "research-work")]
    if research.is_none() && super::live_symbolic::config().is_some() {
        return None;
    }
    #[cfg(feature = "research-work")]
    let config = research
        .map(|(config, _)| config)
        .or_else(|| configured(options))?;
    #[cfg(not(feature = "research-work"))]
    let config = configured(options)?;
    if cache.mode() != CacheMode::Off {
        return None;
    }
    let deadline = DEADLINE.get();
    let late = || deadline.is_some_and(|(clock, budget)| clock.elapsed() >= budget);
    let stop = || observer_stop() || late();
    let job = LiveJob {
        basis,
        pairs,
        max_rows: options.max_matrix_rows,
        selection: options.reducer_selection,
        multiples: options.pair_multiples,
        config,
        scratch: &mut cache.intern,
        limits: Limits {
            entry_allowance: options.live_entry_allowance::<F>(),
            bytes_per_entry: F4Options::bytes_per_entry::<F>(),
            stop: &stop,
        },
    };
    let (result, _report) = F::run_concurrent(job).ok()?;
    #[cfg(feature = "research-work")]
    if let Some((config, mut total)) = research {
        accumulate(&mut total, &_report);
        LIVE.set(Some((config, total)));
    }
    // Under the shipped option a batch whose scratch does not fit the allowance takes the serial
    // closure, as a forward-elimination reservation that does not fit runs serially (#752): the
    // parallel path never refuses what the serial path admits. A research override refuses, so
    // the #872 charge stays observable.
    #[cfg(feature = "research-work")]
    let overridden = research.is_some();
    #[cfg(not(feature = "research-work"))]
    let overridden = false;
    if !overridden && matches!(result, Err(Refusal::LiveEntries { .. })) {
        return None;
    }
    let millis = |d: Duration| d.as_millis().min(u128::from(u64::MAX)) as u64;
    Some(result.map_err(|refusal| match refusal {
        Refusal::Rows(exceeded) => F4Error::TooManyRows {
            limit: exceeded.limit,
        },
        Refusal::LiveEntries { entries } => options.entry_budget_error::<F>(entries),
        Refusal::Stopped if observer_stop() => F4Error::StoppedByObserver,
        Refusal::Stopped => {
            let (clock, budget) = deadline.expect("only the deadline or the observer stops");
            F4Error::TimeBudgetExceeded {
                degree: pairs.iter().map(|pair| pair.degree).max().unwrap_or(0),
                elapsed_millis: millis(clock.elapsed()),
                budget_millis: millis(budget),
            }
        }
    }))
}
