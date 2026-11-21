//! M31-S2 (#904): one batch's elimination under #902's "prereduce + claim" schedule
//! (`docs/research/m31-parallel-signature-elimination.md` §3, §12).
//!
//! Phase A reduces every target against the reducer block alone, in parallel (design 2). The
//! cascade pass then takes targets in signature order. At an entry with no admissible reducer, a
//! target applies the column owner's final row if an earlier target owns the column; otherwise it
//! waits until every earlier target has announced its lead or ended zero, after which owner slots
//! are authoritative. It applies only rows of design 1's pivot map `P_k` and stops only with no
//! entry in `dom P_k`, which are Theorem 1's two conditions, so every row equals design 1's.
//!
//! Termination: every wait is on a smaller rank, the smallest unfinished target never waits, and
//! targets are taken in rank order by running workers, so some worker always progresses.
//!
//! Publication (E1), without `unsafe`: a final row is a `OnceLock` (release on set, acquire on
//! get). A target stores its owner slot (release) before announcing; announcing sets the target's
//! flag and advances the counter over every consecutive set flag. Flag stores, counter loads and
//! the counter's compare-exchange are all `SeqCst`, so of two targets announcing out of rank order
//! at least one sees the other's flag and the counter never stalls below a set flag. A reader that
//! loads (acquire) a counter past `j` therefore sees `j`'s slot.

use std::{
    cmp::Ordering,
    mem::size_of,
    sync::{
        atomic::{
            AtomicBool, AtomicU32, AtomicU64, AtomicU8, AtomicUsize,
            Ordering::{Acquire, Relaxed, Release, SeqCst},
        },
        Barrier, Mutex, OnceLock,
    },
    time::{Duration, Instant},
};

use super::{
    engine::{Reduced, ReducerBlock, Workspace, NONE},
    signature::Signature,
};
use crate::{fields::ConcurrentJob, FiniteField};

/// How a target ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    Zero,
    Singular,
    Element,
}

/// A target's final row: monic for an element, as reduced otherwise (design 1's convention).
pub(super) struct Outcome<F> {
    pub(super) kind: Kind,
    pub(super) row: Vec<(u32, F)>,
    pub(super) products: u64,
}

/// Why a batch was abandoned. Nothing of it reaches the basis (E3).
#[derive(Debug)]
pub(super) enum Stop {
    Wall,
    LiveBytes { bytes: usize, limit: usize },
}

pub(super) struct Report<F> {
    pub(super) outcomes: Vec<Outcome<F>>,
    pub(super) announcement_waits: u64,
    pub(super) final_waits: u64,
    pub(super) peak_live_bytes: usize,
    /// Wall of phase A (to the barrier) and of the cascade pass.
    pub(super) phase_a: Duration,
    pub(super) cascade: Duration,
}

pub(super) struct Claim<'a, const N: usize, F> {
    pub(super) block: &'a ReducerBlock<'a, N, F>,
    pub(super) targets: &'a [(Signature<N>, Vec<(u32, F)>)],
    pub(super) workers: usize,
    pub(super) check: bool,
    pub(super) deadline: Option<Instant>,
    pub(super) live_limit: Option<usize>,
    /// The batch's sparse rows, already allocated.
    pub(super) fixed_bytes: usize,
    #[cfg(test)]
    pub(super) adversary: Option<Adversary>,
}

const RUNNING: u8 = 0;
const WALL: u8 = 1;
const LIVE: u8 = 2;
/// Safe points between deadline reads.
const POLL: u32 = 1024;

/// One value per cache line, so a worker polling a slot does not share a line another writes.
#[repr(align(128))]
struct Padded<T>(T);

/// State the workers share for one batch.
struct Shared<F> {
    pre: Vec<Mutex<Option<Reduced<F>>>>,
    finals: Vec<Padded<OnceLock<Outcome<F>>>>,
    owner: Vec<AtomicU32>,
    announced: Vec<AtomicBool>,
    /// Every target below this rank has announced.
    counter: AtomicUsize,
    next_a: AtomicUsize,
    next_c: AtomicUsize,
    stop: AtomicU8,
    stop_bytes: AtomicUsize,
    live: AtomicUsize,
    peak: AtomicUsize,
    announcement_waits: AtomicU64,
    final_waits: AtomicU64,
    barrier_passed: OnceLock<Instant>,
    #[cfg(test)]
    safe_points: AtomicU64,
}

impl<F> Shared<F> {
    fn stopped(&self) -> bool {
        self.stop.load(Relaxed) != RUNNING
    }

    fn halt(&self, reason: u8) {
        let _ = self.stop.compare_exchange(RUNNING, reason, SeqCst, SeqCst);
    }

    fn charge(&self, bytes: usize, limit: Option<usize>) {
        let now = self.live.fetch_add(bytes, Relaxed) + bytes;
        self.peak.fetch_max(now, Relaxed);
        if limit.is_some_and(|limit| now > limit) {
            self.stop_bytes.fetch_max(now, Relaxed);
            self.halt(LIVE);
        }
    }

    /// Target `k` has its lead (or ended zero): set its flag, then advance the counter past every
    /// consecutive announced rank.
    fn announce(&self, k: usize) {
        self.announced[k].store(true, SeqCst);
        let mut c = self.counter.load(SeqCst);
        while c < self.announced.len() && self.announced[c].load(SeqCst) {
            match self.counter.compare_exchange(c, c + 1, SeqCst, SeqCst) {
                Ok(_) => c += 1,
                Err(now) => c = now,
            }
        }
    }
}

/// Spins, then yields; reads the deadline every [`POLL`] rounds. False once the batch stops.
fn backoff<F>(shared: &Shared<F>, round: &mut u32, deadline: Option<Instant>) -> bool {
    *round = round.wrapping_add(1);
    if *round < 64 {
        std::hint::spin_loop();
    } else {
        std::thread::yield_now();
    }
    if round.is_multiple_of(POLL) && deadline.is_some_and(|d| Instant::now() >= d) {
        shared.halt(WALL);
    }
    !shared.stopped()
}

impl<const N: usize, F: FiniteField> Claim<'_, N, F> {
    fn entry_bytes(row: &[(u32, F)]) -> usize {
        std::mem::size_of_val(row)
    }

    fn run_with(
        &self,
        workers: usize,
        spawn: impl FnOnce(&Shared<F>, &Barrier),
    ) -> Result<Report<F>, Stop> {
        let m = self.targets.len();
        let ncols = self.block.ncols;
        let shared = Shared {
            pre: (0..m).map(|_| Mutex::new(None)).collect(),
            finals: (0..m).map(|_| Padded(OnceLock::new())).collect(),
            owner: (0..ncols).map(|_| AtomicU32::new(NONE)).collect(),
            announced: (0..m).map(|_| AtomicBool::new(false)).collect(),
            counter: AtomicUsize::new(0),
            next_a: AtomicUsize::new(0),
            next_c: AtomicUsize::new(0),
            stop: AtomicU8::new(RUNNING),
            stop_bytes: AtomicUsize::new(0),
            live: AtomicUsize::new(0),
            peak: AtomicUsize::new(0),
            announcement_waits: AtomicU64::new(0),
            final_waits: AtomicU64::new(0),
            barrier_passed: OnceLock::new(),
            #[cfg(test)]
            safe_points: AtomicU64::new(0),
        };
        let metadata = m
            * (size_of::<Mutex<Option<Reduced<F>>>>()
                + size_of::<Padded<OnceLock<Outcome<F>>>>()
                + size_of::<AtomicBool>())
            + ncols * size_of::<AtomicU32>();
        let workspaces = workers * Workspace::<F>::bytes(ncols);
        shared.charge(self.fixed_bytes + metadata + workspaces, self.live_limit);
        if self.deadline.is_some_and(|d| Instant::now() >= d) {
            shared.halt(WALL);
        }
        let barrier = Barrier::new(workers);
        let started = Instant::now();
        spawn(&shared, &barrier);
        let ended = Instant::now();
        let passed = shared.barrier_passed.get().copied().unwrap_or(ended);
        match shared.stop.load(SeqCst) {
            RUNNING => {}
            WALL => return Err(Stop::Wall),
            _ => {
                return Err(Stop::LiveBytes {
                    bytes: shared.stop_bytes.load(SeqCst),
                    limit: self.live_limit.unwrap_or(usize::MAX),
                })
            }
        }
        Ok(Report {
            outcomes: shared
                .finals
                .into_iter()
                .map(|f| f.0.into_inner().expect("every target finished"))
                .collect(),
            announcement_waits: shared.announcement_waits.into_inner(),
            final_waits: shared.final_waits.into_inner(),
            peak_live_bytes: shared.peak.into_inner(),
            phase_a: passed - started,
            cascade: ended - passed,
        })
    }

    /// The pass on the calling thread alone, for a field that cannot cross threads.
    pub(super) fn serial(self) -> Result<Report<F>, Stop> {
        self.run_with(1, |shared, barrier| self.worker(shared, barrier))
    }

    fn worker(&self, shared: &Shared<F>, barrier: &Barrier) {
        let m = self.targets.len();
        if shared.stopped() {
            barrier.wait();
            return;
        }
        let mut workspace = Workspace::new(self.block.ncols);
        loop {
            let k = shared.next_a.fetch_add(1, Relaxed);
            if k >= m || shared.stopped() {
                break;
            }
            let (t, entries) = &self.targets[k];
            let mut polls = 0;
            let done = workspace.reduce(entries, |c| {
                if self.safe_point(shared, &mut polls, k) {
                    return None;
                }
                self.block.admissible(c, t)
            });
            shared.charge(Self::entry_bytes(&done.0), self.live_limit);
            *shared.pre[k].lock().expect("never poisoned") = Some(done);
        }
        if barrier.wait().is_leader() {
            let _ = shared.barrier_passed.set(Instant::now());
        }
        loop {
            let k = shared.next_c.fetch_add(1, Relaxed);
            if k >= m || shared.stopped() {
                break;
            }
            self.finish(shared, &mut workspace, k);
        }
    }

    /// A pivot safe point: the adversary's hook, and the deadline every [`POLL`] calls. True once
    /// the batch stops; the caller then drains its row without further reduction.
    fn safe_point(&self, shared: &Shared<F>, polls: &mut u32, k: usize) -> bool {
        *polls = polls.wrapping_add(1);
        #[cfg(test)]
        if let Some(adversary) = &self.adversary {
            adversary.pause(k, u64::from(*polls), 0);
            let seen = shared.safe_points.fetch_add(1, Relaxed) + 1;
            if adversary.cancel_after.is_some_and(|n| seen >= n) {
                shared.halt(WALL);
            }
        }
        #[cfg(not(test))]
        let _ = k;
        if polls.is_multiple_of(POLL) && self.deadline.is_some_and(|d| Instant::now() >= d) {
            shared.halt(WALL);
        }
        shared.stopped()
    }

    /// Target `k`'s cascade pass from its phase-A row; publishes its outcome unless the batch stops.
    fn finish(&self, shared: &Shared<F>, workspace: &mut Workspace<F>, k: usize) {
        let (t, _) = &self.targets[k];
        let order = self.block.order;
        let (entries, early) = shared.pre[k]
            .lock()
            .expect("never poisoned")
            .take()
            .expect("phase A reduced every target");
        if self.deadline.is_some_and(|d| Instant::now() >= d) {
            shared.halt(WALL);
        }
        #[cfg(test)]
        if let Some(adversary) = &self.adversary {
            adversary.hold(k, self.targets.len());
        }
        let mut known = false;
        let mut lead = false;
        let mut polls = 0;
        let (mut row, later) = workspace.reduce(&entries, |c| {
            if self.safe_point(shared, &mut polls, k) {
                return None;
            }
            if let Some(pivot) = self.block.admissible(c, t) {
                if self.check {
                    let r = self.block.at[c] as usize;
                    assert_eq!(
                        self.block.sigs[r].cmp_in(t, order),
                        Ordering::Less,
                        "a reducer pivot must have a smaller signature"
                    );
                }
                return Some(pivot);
            }
            let mut j = shared.owner[c].load(Acquire);
            if !known && (j == NONE || j as usize > k) {
                // Either the slot fills with an earlier owner (write-once, so authoritative at
                // once) or every earlier target announces and an empty slot means no owner. A
                // later target cannot fill the slot first: it announces only after `k` does.
                let mut round = 0;
                let mut waited = false;
                loop {
                    if shared.counter.load(Acquire) >= k {
                        known = true;
                        j = shared.owner[c].load(Acquire);
                        break;
                    }
                    j = shared.owner[c].load(Acquire);
                    if j != NONE && (j as usize) < k {
                        break;
                    }
                    if !waited {
                        waited = true;
                        shared.announcement_waits.fetch_add(1, Relaxed);
                    }
                    if !backoff(shared, &mut round, self.deadline) {
                        return None;
                    }
                }
            }
            if j != NONE && (j as usize) < k {
                let j = j as usize;
                let mut round = 0;
                if shared.finals[j].0.get().is_none() {
                    shared.final_waits.fetch_add(1, Relaxed);
                }
                let pivot = loop {
                    if let Some(done) = shared.finals[j].0.get() {
                        break done;
                    }
                    if !backoff(shared, &mut round, self.deadline) {
                        return None;
                    }
                };
                assert_eq!(pivot.kind, Kind::Element, "only an element is a pivot (E2)");
                if self.check {
                    assert_eq!(
                        self.targets[j].0.cmp_in(t, order),
                        Ordering::Less,
                        "an earlier target must have a smaller signature"
                    );
                }
                return Some(pivot.row.as_slice());
            }
            if !lead {
                lead = true;
                shared.owner[c].store(k as u32, Release);
                #[cfg(test)]
                if let Some(adversary) = &self.adversary {
                    adversary.pause(k, u64::from(polls), adversary.slow_announcement);
                }
                shared.announce(k);
                #[cfg(test)]
                if let Some(adversary) = &self.adversary {
                    adversary.pause(k, u64::from(polls), adversary.slow_publication);
                }
            }
            None
        });
        if !lead {
            shared.announce(k);
        }
        if shared.stopped() {
            return;
        }
        let kind = self.block.classify(t, &row);
        if kind == Kind::Element {
            let inverse = row[0].1.inverse();
            for (_, v) in &mut row {
                *v *= inverse;
            }
        }
        shared.charge(Self::entry_bytes(&row), self.live_limit);
        let published = shared.finals[k].0.set(Outcome {
            kind,
            row,
            products: early + later,
        });
        assert!(published.is_ok(), "a target is finished once");
    }
}

impl<const N: usize, F: FiniteField> ConcurrentJob<F> for Claim<'_, N, F> {
    type Output = Result<Report<F>, Stop>;

    fn run(self) -> Self::Output
    where
        F: Send + Sync,
    {
        let workers = self.workers.min(self.targets.len()).max(1);
        self.run_with(workers, |shared, barrier| {
            std::thread::scope(|scope| {
                for _ in 1..workers {
                    scope.spawn(|| self.worker(shared, barrier));
                }
                self.worker(shared, barrier);
            });
        })
    }
}

/// Deterministic adverse scheduling for the tests (plan §9.2): seeded yields at every safe point,
/// later targets let ahead, and delays around announcement and publication.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Adversary {
    pub(crate) seed: u64,
    /// Yield at a safe point with probability `yield_permille / 1000`.
    pub(crate) yield_permille: u64,
    /// Hold target `k` back by `(targets − k)` yields before its cascade pass, so later targets
    /// reach their waits first.
    pub(crate) reverse: bool,
    /// Yields between storing a lead's owner slot and announcing it.
    pub(crate) slow_announcement: u64,
    /// Yields between announcing a lead and finishing the row: readers must wait on the final row.
    pub(crate) slow_publication: u64,
    /// Stop as on a crossed wall budget after this many safe points.
    pub(crate) cancel_after: Option<u64>,
}

#[cfg(test)]
impl Adversary {
    fn mix(&self, k: usize, step: u64) -> u64 {
        let mut z = self.seed ^ ((k as u64) << 32) ^ step.wrapping_mul(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn pause(&self, k: usize, step: u64, extra: u64) {
        let draw = self.mix(k, step);
        let yields = extra + u64::from(draw % 1000 < self.yield_permille) * (1 + (draw >> 40) % 8);
        for _ in 0..yields {
            std::thread::yield_now();
        }
    }

    fn hold(&self, k: usize, targets: usize) {
        if self.reverse {
            for _ in 0..(targets - k) * 4 {
                std::thread::yield_now();
            }
        }
    }
}
