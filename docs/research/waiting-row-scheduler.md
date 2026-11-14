# Waiting-row scheduler feasibility (#729)

**Source audit:** `b9898c9a` (2026-11-13), including production candidate-only reduction #749.
**Measured at:** no new measurements. Reanalysis of #728's `cf92a3cb64aaa56346b68c19b8db5dc99f5ae383`
parallel cohort and #747's `ff15a0afa463c31cbeee0dac7f9163e09d1c70c8` forward/backward crossing.
The latter controller is `1bf48baa306070ca7761aa025f5967873204f3db`.
**Decision:** defer a second scheduler; retain dynamic CAS as the experimental comparator.
This completes the bounded feasibility gate, not a queue implementation or production adoption.

## Mechanisms and source findings

| Mechanism | Primary source / inspected boundary | Consequence |
|---|---|---|
| GBLA waiting rows | [Paper §5.1](https://arxiv.org/html/1602.06097#S5.SS1) and [pinned worker, lines 2731–2898](https://github.com/ederc/gbla/blob/2f8ebcf5bab0012b2e3b0acd2842aedde092d9c0/src/elimination.c#L2731-L2898) | Retains residuals and last-applied pivot; ordered completion enables publication. Waiting rows receive preference after progress. This changes dependency order, not just the work container. |
| Structured split / operation order | Paper §§4.1, 4.3–4.4 | Reducer-block treatment and operation ordering are separate from scheduling. Zeebra already splits reducer/candidate rows; #50's rejected eager identity-prefix work stays rejected. |
| Multilines | Paper §4.2 and `echelonize_one_row` at pinned source lines 2901–3039 | Packs multiple rows and changes arithmetic/storage. A queue comparison must keep Zeebra's representation; upstream speedups do not isolate a scheduler. |
| Optional finishing | Paper's echelon target versus Zeebra `src/grobner/f4/reduction.rs` | Current F4 selects new-leading-column output; public linalg retains full RREF. Changing output necessity is #749, not a queue gain. |
| Zeebra CAS | `src/linalg/concurrent.rs`, reduction loop and failed `OnceLock::set` arm | An unsuccessful publisher reloads its **losing residual**, not the original input. Its leading column advances after winner reduction. Previously cleared columns are not restarted. |

The paper describes GBLA as GPLv2; the inspected `elimination.c` header separately declares
LGPL-2.1-or-later. Both are external algorithm references only; no implementation is imported.
The issue's old line anchor 2902–3043 points to row arithmetic, not the waiting-list worker.

## What the retained evidence actually says

The [offline extraction](../../research/waiting-row/evidence.json) retains input archive SHA256,
measurement source, counts, min/max and medians. It decodes content-addressed payloads with
`study_artifacts.load_study`. Existing full-answer validators are rerun separately; status labels
alone are not independent verification. [Reproduction](../../research/waiting-row/README.md).

Historical #728 counters-on diagnostics, five fresh processes per cell:

| Field | Schedule / workers | Forward products | Lost publications | Products after first loss / total | Dominant-batch duration balance |
|---|---|---:|---:|---:|---:|
| 32003 | dynamic / 16 | 578,354,208 | 569 | 5.94% | 0.987 |
| 32003 | static / 16 | 622,277,258 | 168 | 0.33% | 0.636 |
| 2147483647 | dynamic / 16 | 576,824,272 | 750 | 6.98% | 0.985 |
| 2147483647 | static / 16 | 614,764,387 | 322 | 0.57% | 0.633 |
| 32003 | dynamic / 64 | 560,401,051 | 928 | 13.52% | 0.874 |
| 2147483647 | dynamic / 64 | 554,372,312 | 1475 | 16.58% | 0.865 |

Each fraction is calculated within each attempt then summarized; it need not equal a ratio
of independently summarized medians. `worker_duration_balance = sum(worker_ns)/(p*max(worker_ns))`
on the batch with most products. It describes duration spread, **not CPU utilization, idle time
or critical-path slack**: clocks can include descheduling, locks and OS delays. The archive has
no separate idle/wait distribution. High balance does not prove absent contention.

Static p=16 incurs fewer losses yet more total products and greater duration spread. Thus
minimizing loss count is not a justified scheduler objective. Dynamic p=16's scheduling/reservation
worker-clock sums are 0.836/0.369 ms and publication sums 0.322/0.386 ms. These instrumented,
possibly overlapping clocks are not elapsed fractions or a safe ceiling on all scheduler effects.
`retry_products` begins after the **first** failed publication and includes every subsequent
pivot subtraction for that input, even essential reductions. It is neither avoided work nor a
count of repeated applications of the same pivot.

The [original report](concurrent-pivots.md) retains whole-process timing, CPU, RSS, matrix identity,
full-basis checks, small-case regressions and MQ14 refusals. Both p=4 MQ14 fields refused the
entry budget; no scheduler has demonstrated a larger fixed-budget completion. Higher core counts
alone do not resolve that frontier.

## Post-selection conditioning and cost gate

#747's four-worker crossing includes selected backward output; it is an experimental policy,
not a measurement of #749 production or #752 adaptive integration. Its separate work-on pilot
contains **one** observation per field/arm, not five repeated timings:

| Field, parallel-selected | Forward products | Lost publications | Post-loss product subset | Duration balance | Reserved entries / workspace bytes |
|---|---:|---:|---:|---:|---:|
| 32003 | 584,134,280 | 183 | 1.44% | 0.9966 | 1,571,889 / 865,440 |
| 2147483647 | 584,319,879 | 184 | 1.24% | 0.9983 | 1,573,215 / 1,057,760 |

Separate counters-off five-process timing arms support a **conditional model**. For each attempt,
let `T` be process wall and `F` the summed forward-call wall. With unchanged outside work,
eliminating all forward work would bound speedup by `T/(T-F)`. This unrealistic all-forward
ceiling is 2.328x/2.364x for the four-worker selected arms, versus 1.145x/1.149x with full backward
output. Removing backward work substantially changes the opportunity; multiplying old speedups
is invalid. These are reduced-basis processes including answer rendering, not complete solving.

For the M28 gate of at least **10% reduction in complete-task wall**, a scheduler saving `dF`
of forward time while adding `Q` queue overhead must satisfy:

`dF - Q >= 0.10*T`, hence `dF/F >= 0.10*T/F + Q/F`.

Calculated per attempt, the selected crossing requires median **17.53%/17.33%** forward saving
even with free queue operations. This is a falsifiable required opportunity, not a prediction.
Under an explicitly unvalidated proportional-cost assumption, deleting even the entire 1.44%/1.24%
post-loss product subset is far short of that requirement. The assumption is not an elapsed bound:
normalization, loads, scans, cache behavior and changed winners can dominate. A proposal relying
on those effects must measure them; absence of traces does not establish negligible contention.

#592's [persistent-worker evidence](worker-pool.md) distinguishes constructor, dispatch, scratch
and whole-border costs. Its owned independent FGLM jobs are not dependent F4 residuals; neither
its pool floor nor #728 scoped-thread spawn/join floor can price queue reenqueue/wakeup costs.
Keep arithmetic, pool, budgets and output fixed in any future comparator.

## Ordering, ownership and progress requirements

A plausible independent design can use an **input-row completion frontier**, rather than treating
an empty column slot as something that must eventually acquire a pivot. Let `f` be the first input
row not finalized. Rows below `f` have finalized either a monic pivot or zero. Maintain an immutable
publication sequence for their nonzero pivots. Each live row owns a residual and a cursor into that
sequence. Reduce it only against new entries, preserving the row-span relation to its original input.
For this cursor to be sound, every newly published pivot must have zero coefficients in **all**
previous publication pivot columns, and applying an entry must clear its pivot coefficient even
when it is not the residual's current lead. Then a later pivot cannot reintroduce a column the
cursor already passed. A leading-column-only CAS stopping rule does not provide this stronger
invariant for an arbitrary append order; copying that rule into a queue would be incorrect.
This proposal may therefore change arithmetic and pivot finishing as well as scheduling, and
those costs/trajectory changes must be separately charged, not called equal-work queue savings.

A row with index `f` may finalize after applying the entire published sequence; a later row must
wait for preceding input rows, even if its current lead slot is empty. Zero rows **advance the input
frontier without adding a pivot**. Separating these two counters prevents rank-deficient termination
from waiting for a nonexistent pivot. A nonzero finalized residual has a unique leading column;
retain it immutable until all readers join, then sort/extract and perform the selected or full
backward output required by the caller. A final reduced basis still needs exact independent checking.

Each input row occupies exactly one state: unstarted, uniquely worker-owned, queued, or finalized.
A bounded queue has at most the number of candidate rows. Use one ownership transfer under a lock;
a row cannot be simultaneously queued and worker-owned. Queue entries carry residual ownership,
cursor and the publication generation last observed. Prefer `f` whenever ready; ties use input
index or another starvation-free rule. If a worker finds no new generation, it must sleep or run
the frontier row, not busy-reenqueue the same residual. Publication/frontier advance increments
a generation and wakes waiters under a condition-variable protocol that rechecks its predicate
under the lock, preventing lost wakeups.

There is always a next frontier row until all inputs finalize. Under fair worker scheduling its
finite reductions complete; this advances `f`, including through zeros. Induction over input index
proves termination, provided the scheduler never evicts the frontier in favor of blocked later
rows. Cancellation or panic instead wakes everyone, joins all readers and discards the result;
no completion is accepted until all workers succeed. Mutex poisoning must be converted to failure,
not leave sleeping workers. A later implementation needs forced schedules to test these conditions;
this argument is a design constraint, not proof of unimplemented code.

This ordering can serialize a long early row even when later pivots could win under CAS. It also
requires storage for queued residuals. The current CAS reservation covers active worker residuals;
with `k` suspended dense residuals it cannot silently cover only `p` active rows. Charge suspended
support and capacity, index/cursor/queue storage, simultaneous conversions and wakeup bookkeeping
before growth, with checked overflow and failure cleanup. Alternatively bounded sparse suspension
must charge gathers/loads and retained capacity. At most `rows*columns*sizeof(F)` coefficient storage
is a coarse dense-suspension upper bound, potentially much larger than `p*columns*sizeof(F)`.
This maintenance and memory cost needs evidence of an end-to-end opportunity before a prototype.

## Decision and acceptance disposition

**Defer the waiting-row prototype at this gate.** Dynamic CAS remains the single experimental
strategy selected for #752. Current evidence favors its load distribution over static contiguous
rows; it does not show a queue-addressable elapsed bottleneck. This is not a claim queues are
slower or contention is negligible. No dual scheduler, priority or work-stealing policy is added.

| #729 acceptance | Disposition |
|---|---|
| Paper/source mechanism table | Met above; immutable source and corrected worker anchor. |
| Quantitative opportunity or reason to stop | Met: post-selection required saving model, observed subset limits, missing attribution and suspension cost support scoped defer. |
| Queue prototype/race/scaling/full-answer comparison | Conditional, not run: gate does not justify a second implementation. Existing CAS/reference evidence is retained separately. |
| Complete F4 and fixed-budget decision | Defer: no queue speedup or new frontier; preserve exact MQ14 refusals. |

Reopen only after #752/#751 pins an integrated candidate-only dynamic comparator, with worker-local
CPU/blocked time, tail imbalance, publication losses, useful products and memory charged separately.
A bounded pilot must identify an avoidable mechanism large enough for `dF-Q >= 0.10*T` on the actual
complete task (or a predeclared fixed-budget verified frontier benefit). Use matched runtime,
arithmetic and output; retain p=1, public small controls, five interleaved fresh-process timing
repetitions and separate diagnostics. Adoption still requires no more than 5% material control
regression and at most 1.25x RSS unless justified in advance. No further campaign or larger memory
allowance follows from this report. If measurements cannot support the opportunity, retain this
defer decision rather than funding a second scheduler from loss counts alone.
