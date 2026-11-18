//! #902's replay of the cross-target cascade: per batch, the column-ordered trace of every
//! target's reduction, reduced at batch end to dependency statistics and the critical path of
//! three schedules (`docs/research/m31-parallel-signature-elimination.md` §5).
//!
//! It only observes. The engine's call sites run whether or not a recording is active, nothing
//! here feeds back into elimination, and times are in coefficient products — a ceiling model, not
//! a clock. Recording is per thread: the serial pass runs on the caller's thread.

use std::cell::RefCell;

thread_local! {
    static ACTIVE: RefCell<Option<Vec<BatchRecord>>> = const { RefCell::new(None) };
}

/// Runs `f` with recording on for this thread and returns one record per eliminated batch.
pub fn record<R>(f: impl FnOnce() -> R) -> (R, Vec<BatchRecord>) {
    ACTIVE.with(|a| *a.borrow_mut() = Some(Vec::new()));
    let result = f();
    let records = ACTIVE.with(|a| a.borrow_mut().take()).unwrap_or_default();
    (result, records)
}

/// How a parallel cascade decides that a target's surviving entry at column `c` is final.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Schedule {
    /// Waits only for the final rows it applies. Not a valid schedule alone: it is the bound for
    /// any schedule that applies final rows, displacement included (§5.4).
    Dag,
    /// Exact: waits until every earlier target has passed `c` or announced its lead (§5.2).
    Frontier,
    /// Exact: at its first surviving entry, waits until every earlier target has announced its
    /// lead or finished as a zero row; every later column is then known (§5.3).
    Claim,
}

pub const SCHEDULES: [Schedule; 3] = [Schedule::Dag, Schedule::Frontier, Schedule::Claim];

impl Schedule {
    pub fn name(self) -> &'static str {
        match self {
            Self::Dag => "dag",
            Self::Frontier => "frontier",
            Self::Claim => "claim",
        }
    }

    fn slot(self) -> usize {
        self as usize
    }
}

/// One batch's cascade, in coefficient products.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BatchRecord {
    pub columns: usize,
    pub targets: usize,
    pub zero_targets: usize,
    /// Pivot applications by a reducer-block row, and by an earlier target's result.
    pub reducer_steps: u64,
    pub target_steps: u64,
    /// Entries left in place: no admissible pivot at their column.
    pub surviving: u64,
    /// Reducer-block applications at a column an earlier target already leads: two admissible
    /// rows share a lead there, the case where only design 1's own rows are pinned (§4.3).
    pub shadowed: u64,
    /// Products spent before the signature-ordered pass (design 2's parallel pre-reduction).
    pub phase_a: u64,
    pub max_phase_a: u64,
    /// Products in the signature-ordered pass.
    pub cascade: u64,
    pub max_target: u64,
    /// Targets that apply at least one earlier target's result.
    pub dependent_targets: usize,
    /// Distinct (earlier, later) target pairs with a use.
    pub edges: usize,
    /// Longest chain of target-on-target uses, in targets, and the most targets at one depth.
    pub depth: usize,
    pub width: usize,
    /// Infinite-worker makespan per [`Schedule`], indexed by `Schedule as usize`.
    pub critical: [u64; 3],
    /// Uses where, on the [`Schedule::Dag`] timeline, the later target reaches the column before
    /// the earlier one has claimed it: a least-signature-wins claim would displace there.
    pub would_displace: u64,
    /// Products the displaced rows had spent past the contested column: the most a displacement
    /// could redo.
    pub displaced_suffix: u64,
}

impl BatchRecord {
    pub fn work(&self) -> u64 {
        self.phase_a + self.cascade
    }

    /// Makespan bound `max(CP, W/p)` and Graham's greedy guarantee `W/p + (1 − 1/p)·CP`.
    pub fn makespan(&self, schedule: Schedule, workers: usize) -> (f64, f64) {
        let (w, cp, p) = (
            self.work() as f64,
            self.critical[schedule.slot()] as f64,
            workers.max(1) as f64,
        );
        (cp.max(w / p), w / p + (1.0 - 1.0 / p) * cp)
    }

    /// Design 2 as shipped: parallel pre-reduction, then the whole cascade on one thread.
    pub fn serial_cascade_makespan(&self, workers: usize) -> (f64, f64) {
        let (a, max_a, p) = (
            self.phase_a as f64,
            self.max_phase_a as f64,
            workers.max(1) as f64,
        );
        let c = self.cascade as f64;
        (max_a.max(a / p) + c, a / p + (1.0 - 1.0 / p) * max_a + c)
    }
}

const REDUCER: u32 = 0;
const TARGET: u32 = 1 << 30;
const SURVIVING: u32 = 2 << 30;
const KIND: u32 = 3 << 30;

/// A pivot application or a surviving entry; `packed` is the products (≤ 2³⁰) and a kind tag.
#[derive(Clone, Copy)]
struct Step {
    column: u32,
    packed: u32,
}

impl Step {
    fn cost(self) -> u64 {
        u64::from(self.packed & !KIND)
    }

    fn kind(self) -> u32 {
        self.packed & KIND
    }
}

struct Trace {
    offset: u64,
    steps: Vec<Step>,
}

/// The engine-side handle for one batch; inert unless [`record`] is active on this thread.
pub(super) struct Recorder {
    on: bool,
    columns: usize,
    /// The target whose lead is at each column; at most one, singular rows included.
    owner: Vec<u32>,
    traces: Vec<Trace>,
    current: Vec<Step>,
}

const NONE: u32 = u32::MAX;

impl Recorder {
    pub(super) fn new(columns: usize) -> Self {
        let on = ACTIVE.with(|a| a.borrow().is_some());
        Self {
            on,
            columns,
            owner: if on { vec![NONE; columns] } else { Vec::new() },
            traces: Vec::new(),
            current: Vec::new(),
        }
    }

    /// Column `c` was visited with a nonzero entry; `pivot_len` is the applied row's length.
    pub(super) fn step(&mut self, c: usize, pivot_len: Option<usize>, from_target: bool) {
        if !self.on {
            return;
        }
        let packed = match pivot_len {
            None => SURVIVING,
            Some(len) => {
                let cost = u32::try_from(len - 1).expect("a row of under 2³⁰ entries");
                assert!(cost < TARGET, "a row of under 2³⁰ entries");
                cost | if from_target { TARGET } else { REDUCER }
            }
        };
        self.current.push(Step {
            column: c as u32,
            packed,
        });
    }

    /// Closes the current target: `earlier` products spent before this pass, `lead` its first
    /// surviving column.
    pub(super) fn end(&mut self, earlier: u64, lead: Option<u32>) {
        if !self.on {
            return;
        }
        if let Some(lead) = lead {
            let slot = &mut self.owner[lead as usize];
            assert_eq!(*slot, NONE, "two targets lead at one column");
            *slot = self.traces.len() as u32;
        }
        self.traces.push(Trace {
            offset: earlier,
            steps: std::mem::take(&mut self.current),
        });
    }

    pub(super) fn finish(self) {
        if !self.on {
            return;
        }
        let record = self.summarize();
        ACTIVE.with(|a| {
            if let Some(records) = a.borrow_mut().as_mut() {
                records.push(record);
            }
        });
    }

    fn owner_of(&self, step: Step, k: usize) -> usize {
        let u = self.owner[step.column as usize] as usize;
        assert!(u < k, "a target applies only an earlier target's result");
        u
    }

    fn summarize(&self) -> BatchRecord {
        let mut r = BatchRecord {
            columns: self.columns,
            targets: self.traces.len(),
            ..BatchRecord::default()
        };
        let mut depth = vec![0usize; self.traces.len()];
        let mut at_depth: Vec<usize> = Vec::new();
        for (k, trace) in self.traces.iter().enumerate() {
            let mut cost = 0u64;
            let mut uses: Vec<usize> = Vec::new();
            for &s in &trace.steps {
                cost += s.cost();
                match s.kind() {
                    REDUCER => {
                        r.reducer_steps += 1;
                        let owner = self.owner[s.column as usize];
                        r.shadowed += u64::from(owner != NONE && (owner as usize) < k);
                    }
                    TARGET => {
                        r.target_steps += 1;
                        uses.push(self.owner_of(s, k));
                    }
                    _ => r.surviving += 1,
                }
            }
            if !trace.steps.iter().any(|s| s.kind() == SURVIVING) {
                r.zero_targets += 1;
            }
            uses.sort_unstable();
            uses.dedup();
            r.edges += uses.len();
            r.dependent_targets += usize::from(!uses.is_empty());
            depth[k] = 1 + uses.iter().map(|&u| depth[u]).max().unwrap_or(0);
            if at_depth.len() < depth[k] {
                at_depth.resize(depth[k], 0);
            }
            at_depth[depth[k] - 1] += 1;
            r.phase_a += trace.offset;
            r.max_phase_a = r.max_phase_a.max(trace.offset);
            r.cascade += cost;
            r.max_target = r.max_target.max(trace.offset + cost);
        }
        r.depth = at_depth.len();
        r.width = at_depth.iter().copied().max().unwrap_or(0);
        for schedule in SCHEDULES {
            let (critical, displace, suffix) = self.critical_path(schedule);
            r.critical[schedule.slot()] = critical;
            if schedule == Schedule::Dag {
                r.would_displace = displace;
                r.displaced_suffix = suffix;
            }
        }
        r
    }

    /// Infinite-worker list schedule, targets in signature order; every target starts at its own
    /// `offset`. Returns the makespan and, on the DAG timeline, the would-be displacements.
    fn critical_path(&self, schedule: Schedule) -> (u64, u64, u64) {
        let n = self.traces.len();
        let mut done = vec![0u64; n];
        let mut lead_at = vec![0u64; n];
        let mut announced = 0u64;
        let mut frontier = if schedule == Schedule::Frontier {
            vec![0u64; self.columns]
        } else {
            Vec::new()
        };
        let (mut displace, mut suffix) = (0u64, 0u64);
        let mut completions: Vec<(u32, u64)> = Vec::new();
        for (k, trace) in self.traces.iter().enumerate() {
            let total: u64 = trace.steps.iter().map(|s| s.cost()).sum();
            let mut spent = 0u64;
            let mut t = trace.offset;
            let mut lead = None;
            completions.clear();
            for &s in &trace.steps {
                match s.kind() {
                    REDUCER => t += s.cost(),
                    TARGET => {
                        let u = self.owner_of(s, k);
                        if schedule == Schedule::Dag && t < lead_at[u] {
                            displace += 1;
                            suffix += total - spent;
                        }
                        t = t.max(done[u]) + s.cost();
                    }
                    _ => {
                        let wait = match schedule {
                            Schedule::Dag => 0,
                            Schedule::Claim => announced,
                            Schedule::Frontier => frontier[s.column as usize],
                        };
                        t = t.max(wait);
                        lead.get_or_insert(t);
                    }
                }
                spent += s.cost();
                completions.push((s.column, t));
            }
            done[k] = t;
            lead_at[k] = lead.unwrap_or(t);
            announced = announced.max(lead_at[k]);
            if schedule == Schedule::Frontier {
                // Target k has passed column c once its last step at or before c completes,
                // and every column once its lead is announced.
                let (mut j, mut last) = (0, trace.offset);
                for (c, slot) in frontier.iter_mut().enumerate() {
                    while j < completions.len() && completions[j].0 as usize <= c {
                        last = completions[j].1;
                        j += 1;
                    }
                    *slot = (*slot).max(last.min(lead_at[k]));
                }
            }
        }
        (done.iter().copied().max().unwrap_or(0), displace, suffix)
    }
}

/// Totals over a run, and ceilings against a design-1 `baseline` work at `workers`.
pub fn ceiling(
    records: &[BatchRecord],
    baseline: u64,
    schedule: Option<Schedule>,
    workers: usize,
) -> (f64, f64) {
    let (mut bound, mut greedy) = (0.0, 0.0);
    for r in records {
        let (b, g) = match schedule {
            Some(s) => r.makespan(s, workers),
            None => r.serial_cascade_makespan(workers),
        };
        bound += b;
        greedy += g;
    }
    let base = baseline as f64;
    (base / bound.max(1.0), base / greedy.max(1.0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fields::{PrimeFieldElement64, Zp32003},
        grobner::{
            benchmark_systems::{cyclic, katsura},
            sigf4::{sig_f4_reported, SigF4Options, SigF4Statistics},
        },
        poly::MonomialOrder,
        FiniteField, MultivariatePolynomial,
    };

    type Goldilocks = PrimeFieldElement64<18446744069414584321>;

    fn algebraic(s: &SigF4Statistics) -> Vec<u64> {
        [
            s.batches,
            s.pairs_created,
            s.pairs_singular,
            s.rejected_product,
            s.rejected_koszul,
            s.rejected_zero_row,
            s.rejected_rewrite,
            s.rejected_duplicate,
            s.targets,
            s.reducer_rows,
            s.reductions_to_zero,
            s.singular_rows,
            s.elements_added,
            s.signature_basis_elements,
            s.reduced_basis_elements,
            s.syzygy_signatures,
        ]
        .iter()
        .map(|&v| v as u64)
        .chain([
            s.coefficient_products,
            s.products_on_zero_rows,
            s.products_on_singular_rows,
        ])
        .collect()
    }

    fn invariant<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>]) {
        let order = MonomialOrder::GradedReverseLexicographic;
        for workers in [1, 4] {
            let options = SigF4Options {
                workers,
                ..SigF4Options::default()
            };
            let (plain, plain_stats) = sig_f4_reported(system, order, &options);
            let ((recorded, stats), records) = record(|| sig_f4_reported(system, order, &options));
            assert_eq!(recorded.unwrap(), plain.unwrap());
            assert_eq!(algebraic(&stats), algebraic(&plain_stats));
            assert_eq!(records.len(), stats.batches);
            let work: u64 = records.iter().map(BatchRecord::work).sum();
            assert_eq!(work, stats.coefficient_products);
            let zero: usize = records.iter().map(|r| r.zero_targets).sum();
            assert_eq!(zero, stats.zero_rows);
            for r in &records {
                let [dag, frontier, claim] = r.critical;
                assert!(r.max_target <= dag && dag <= frontier && frontier <= claim);
                assert!(claim <= r.work());
            }
        }
    }

    /// Recording changes no basis, statistic or product count, serial or with pre-reduction.
    #[test]
    fn test_recording_changes_no_algebraic_quantity() {
        invariant(&katsura::<6, Goldilocks>());
        invariant(&katsura::<5, Zp32003>());
        invariant(&cyclic::<5, Goldilocks>());
    }

    /// Without an active recording no batch is recorded.
    #[test]
    fn test_inactive_recorder_records_nothing() {
        let mut recorder = Recorder::new(4);
        recorder.step(0, Some(3), false);
        recorder.end(0, Some(1));
        assert!(recorder.traces.is_empty());
        recorder.finish();
        let ((), records) = record(|| ());
        assert!(records.is_empty());
    }

    /// A hand-built batch gives the critical paths each schedule's waiting rule implies.
    #[test]
    fn test_critical_paths_follow_each_waiting_rule() {
        // Target 1, a zero row, meets column `late` last and finishes at 10.
        let batch = |late: usize| {
            let ((), records) = record(|| {
                let mut r = Recorder::new(4);
                // Target 0: 5 products, its lead at column 1, then 1 more: done at 6.
                r.step(0, Some(6), false);
                r.step(1, None, false);
                r.step(2, Some(2), false);
                r.end(0, Some(1));
                r.step(0, Some(2), false);
                r.step(late, Some(10), false);
                r.end(0, None);
                // Target 2 applies target 0's result (final at 6), leads at column 2, then 4 more.
                r.step(1, Some(3), true);
                r.step(2, None, false);
                r.step(3, Some(5), false);
                r.end(0, Some(2));
                r.finish();
            });
            records[0].clone()
        };
        let early = batch(3);
        let shape = (
            early.targets,
            early.zero_targets,
            early.edges,
            early.depth,
            early.width,
        );
        assert_eq!(shape, (3, 1, 1, 2, 2));
        assert_eq!(early.work(), 6 + 10 + 6);
        // Dag: 6 + 2 + 4. Frontier: the zero row passed column 2 at 1, so no wait. Claim: the
        // lead waits for the zero row to finish at 10, then 4 more.
        assert_eq!(early.critical, [12, 12, 14]);
        // On the DAG timeline target 2 reaches column 1 at 0, before target 0 claims it at 5.
        assert_eq!((early.would_displace, early.displaced_suffix), (1, 6));
        // Now the zero row passes column 2 only when it finishes.
        assert_eq!(batch(2).critical, [12, 14, 14]);
        assert_eq!(early.makespan(Schedule::Dag, 2), (12.0, 11.0 + 6.0));
    }
}
