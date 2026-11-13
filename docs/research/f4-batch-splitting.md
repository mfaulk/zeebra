# Bounded F4 construction retry study

**Baseline source:** `a33a192e819f3ed63fed20b6e3df1445cd0fb1f7`.

**Measured at:** `f1158dbad91cb648f3560feaea4209efc28157a4` on 2026-11-13 UTC.

Issue #685 asks whether a construction refusal can recover under unchanged matrix
budgets. This study keeps the shipping solver and its defaults unchanged. The
prototype is `examples/batch_splitting_study.rs`, built only as an example. Its
transactional scheduling is independently implemented from Zeebra's public stage
and pair-queue APIs; no external engine source is incorporated.

## Transaction and termination

`PairQueue::select_batch` pops pairs and records them as handled. The chain
criterion's `filter_batch` masks every selected pair from witnesses during that
batch. Consequently, requeueing only the retained filtered tail after a failed
build would be unsound: selected-but-unreduced pairs could remain handled and
justify a later chain discard.

The prototype leaves the committed queue unchanged and clones it for each
attempt. Selection, filtering and build preflight operate only on the trial.
A failed trial, its symbolic objects and cache are dropped. The next attempt
selects a strictly smaller deterministic prefix from the unchanged committed
queue. Only after construction and reduction succeed, and the deadline has been
checked, does the trial replace the committed queue. Candidate insertion then
uses the ordinary pair insertion and criteria code. Every unselected tail is
already pending, so there is no extra requeue operation or unresolved handled
witness. Stale GM entries are reevaluated through ordinary selection; newly
inserted leading monomials can invalidate pending pairs through the same update
code. Deferred pairs remain unhandled and are promoted before completion.

A split replaces selected size s>1 by floor(s/2), at least one. The global retry
limit is 32 and a one-pair failure terminates. Successful batches either consume
obligations or add a leading monomial outside the current leading ideal, giving
the existing Dickson-lemma termination argument. No failure returns a partial
successful basis. Tests exercise failed-trial chain witnesses, deferred and lazy
stale pairs, duplicates, deterministic tie order, recovery, retry exhaustion,
one-pair impossibility, deadlines and terminal elimination refusal.

## Deliberately conservative implementation

The public `build_batch_matrix` API identifies construction errors before
elimination. Only its row, column, entry and byte refusals are eligible for
splitting. The subsequent `reduce_batch` call rebuilds the successful matrix;
its errors are terminal even when they have the same error type. The cache is
Off on both passes, and their row/column/initial-entry shapes are asserted equal.
The preflight matrix is dropped before reduction. This avoids changing the
shipping stage interface, while explicitly paying a second successful build.

All custom-loop controls share snapshot, preflight/rebuild and final division
costs. The separate `shipping` control uses the real F4 default, including its
order-based final interreduction choice. These are distinct controls; a custom
loop versus shipping ratio cannot isolate splitting. There is no performance
claim from one sample per cell.

The deadline is checked before each attempt, after build, after reduction before
commit, and around final division. A field operation or final division cannot be
interrupted internally by this example. The external process watchdog supplies
the hard stop. Batch and basis limits never cause retries. Successful-but-
uncommitted attempts are retained when a deadline or batch cap stops them.

## Frozen experiment

`tools/external/batch-splitting-study.py` declares exactly 74 fresh-process cells:
ten public or synthetic fixtures, each with shipping and custom unlimited-budget
controls, then shipping/static-unlimited/static-1/static-2/adaptive under a fixed
row allowance; four boundary cells cover impossible construction, zero retries,
column refusal and an elimination entry-budget refusal. The public Cyclic,
Katsura and seeded random-MQ families include homogeneous transforms and their
inhomogeneous originals. Unit and positive-dimensional fixtures complete the
set. Homogenization uses a new last variable and each generator's own total
degree; it does not saturate the homogenized ideal. Random MQ uses seed zero.
The fixture name, original ordered generators and canonical input digest are
retained in every response.

Each cell has a one-worker, 60-second, 2 GiB process-tree RSS watchdog and at
most 32 retries. Address space is not additionally constrained. The runner reuses the
existing `grobx-work-study.py` watchdog and `mq10-profile.py` process-tree memory
reader. A single machine benchmark lock covers the campaign. Each completed
answer is checked coefficient-for-coefficient against a live Singular reduced
basis under identical GF(32003) grevlex input, plus Zeebra's submitted-basis
checks. Exact equality to the complete independently computed reference supplies
the reverse inclusion which submitted-basis checks alone do not establish.

Every stdout, stderr, exit, watchdog stop, process wall/RSS, stage clocks,
compiler/CPU/affinity/lockfile/binary identity and input/result is retained. A
refusal is an outcome. The Rust harness separates solve and verification time;
process wall includes both, source generation and diagnostic output. No rows or
capacities are fabricated for partial failed builds: those are null because the
public error API exposes only the first exceeded bound.

For built matrices the record includes rows, columns, initial entries, entry
capacity and symbolic row/term-handle capacities. Both simultaneously live
committed/trial queue payload lower bounds are recorded. Private queue heap and
hash-table capacities, rank wrapper payload, symbolic hash tables and allocator
overhead are not exposed by the public API; `queue_capacity_bytes` is explicitly
null. RSS and the external cap include these objects, but do not attribute their
peak to an individual failed attempt. Snapshot memory is additional work, not a
memory saving. This study makes no elimination-budget-compliance claim: #659's
broader live-entry/RSS accounting question is explicitly outside the build-only
recovery experiment. Large-matrix/cache scaling remains gated on #640.

## Reproduction

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-685
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=""
mkdir -p "$TMPDIR"
cargo test -j4 --example batch_splitting_study
python3 tools/test/batch-splitting-study-test.py
cargo build -j4 --release --example batch_splitting_study
# Commit the complete instrument, and choose new scratch/output paths for each campaign.
tools/benchlock.sh batch-splitting-685 taskset -c 0 \
  python3 tools/external/batch-splitting-study.py \
  --binary "$CARGO_TARGET_DIR/release/examples/batch_splitting_study" \
  --scratch "$CARGO_TARGET_DIR/replay-scratch" \
  --output "$CARGO_TARGET_DIR/replay.json.gz"
```

Single functional run (requires Singular and GNU `timeout`):
`cargo run --example batch_splitting_study -- cyclic-4 adaptive rows 7`.
`POLICY` is `shipping`, `static-none`, `static1`, `static2` or `adaptive`;
`BUDGET` is `rows`, `columns`, `entries` or `unbounded`, followed by an unsigned
allowance and optional maximum retries in 0..32. `unbounded` ignores the numeric
allowance. The CLI accepts only the declared small fixtures and fixed field.

## Initial infrastructure failure and bounded correction

The first campaign at `b8a9bc2bd9beb50f12184fcca7b65157bd6cbda9` added a 2 GiB
hard address-space limit beyond the issue's RSS requirement. Its first eight
cells failed when Singular timed out with empty output; the campaign was
interrupted during the ninth cell. Every completed and partial stdout/stderr,
command, exit, metadata and lock event is retained in
[`initial-failed`](../../research/batch-splitting/initial-failed/). None is an
accepted solver result. A bounded three-command diagnostic submits the same tiny
Cyclic-3 input on CPU 0: both the installed Singular wrapper and its underlying
ELF time out with the address-space cap, while the uncapped wrapper returns the
exact basis. The diagnostic does not identify which virtual mappings cause the
failure; RSS and address space are different resources.

The corrected runner removes only the additional address-space limit and keeps
the existing 2 GiB process-tree RSS / 60-second watcher, including the independent
verifier. A new source-pinned campaign runs the same declared 74 cells once each
with fresh output paths. Initial failures remain separate and are never pooled
with the corrected run. This is the full declared correction; further runs need
a separately stated bound.

## Corrected outcomes and decision

**Measured at:** `f1158dbad91cb648f3560feaea4209efc28157a4` on 2026-11-13 UTC.

All 74 declared cells ran: 55 complete answers passed exact reference and
submitted-basis checks; 19 returned explicit refusals. There were no external
watchdog stops, process failures or failed verifier checks. The shipping and
custom unlimited-budget controls completed all ten fixtures. The table shows
fixed-row-budget outcomes; `ok` means a fully verified reduced basis, `rows`
is construction refusal, and `one pair` means splitting cannot shrink further.

| Fixture | Rows | Shipping | Custom pair cap ∞ | Static 1 | Static 2 | Adaptive | Retries | Adaptive process ms | Adaptive observed tree MiB |
|---|---:|---|---|---|---|---|---:|---:|---:|
| cyclic-3 | 3 | ok | ok | ok | ok | ok | 0 | 38.28 | 23.98 |
| cyclic-4 | 7 | rows | rows | ok | rows | ok | 4 | 39.05 | 24.45 |
| katsura-2 | 7 | ok | ok | ok | ok | ok | 0 | 39.43 | 21.96 |
| katsura-3 | 18 | rows | rows | ok | rows | ok | 2 | 40.34 | 23.05 |
| mq-random-3 | 18 | ok | ok | ok | ok | ok | 0 | 38.95 | 22.58 |
| mq-homogeneous-3 | 20 | ok | ok | ok | ok | ok | 0 | 36.81 | 22.98 |
| cyclic-homogeneous-4 | 10 | rows | rows | ok | ok | ok | 1 | 38.59 | 23.24 |
| katsura-homogeneous-3 | 20 | rows | rows | ok | ok | ok | 1 | 37.23 | 21.88 |
| unit | 1 | ok | ok | ok | ok | ok | 0 | 37.13 | 21.50 |
| positive-dimensional | 1 | rows | rows | rows | rows | one pair | 0 | 37.42 | 21.68 |

Four workloads recover under the same row allowance after the unlimited-batch
controls refuse: Cyclic-4, Katsura-3 and their homogeneous transforms. Static 1
also completes these four workloads. This supports the narrow proposition that
construction-batch width can cause an otherwise avoidable refusal; it does not
establish an advantage of adaptive splitting over a suitable static cap. The
positive-dimensional fixture under one row cannot construct even one pair and
correctly refuses. Unit input needs no matrix and completes under that allowance.

The four additional boundary outcomes are retained separately:

| Boundary | Outcome | Retries | Process ms | Observed tree MiB |
|---|---|---:|---:|---:|
| Cyclic-4 rows=0, max retries=32 | one-pair | 0 | 37.90 | 22.39 |
| Cyclic-4 rows=7, max retries=0 | retry-limit | 0 | 37.56 | 22.38 |
| Cyclic-4 entries=19, max retries=32 | reduction | 0 | 38.83 | 22.71 |
| Cyclic-4 columns=3, max retries=32 | one-pair | 0 | 37.47 | 21.76 |

The successful adaptive recoveries include the repeated preflight/rebuild work:

| Fixture | Attempts | Failed builds | Selected pairs across attempts | Successful preflight rows | Preflight ms | Reduction plus rebuild ms | Final division ms | Peak reported queue payload lower bound B |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cyclic-4 | 14 | 4 | 20 | 47 | 0.047 | 0.042 | 0.014 | 744 |
| katsura-3 | 8 | 2 | 17 | 89 | 0.067 | 0.073 | 0.018 | 744 |
| cyclic-homogeneous-4 | 8 | 1 | 14 | 43 | 0.027 | 0.040 | 0.015 | 784 |
| katsura-homogeneous-3 | 6 | 1 | 15 | 75 | 0.063 | 0.069 | 0.023 | 784 |

Row totals exclude unknown failed symbolic prefixes. Every successful preflight
is rebuilt once for reduction, and that cost is included in the reduction column.
Private queue capacities remain unknown; the payload figure is a lower bound,
not a workspace budget. Raw records retain every successful matrix entry and
symbolic capacity, filtered/selected count, and provisional handled count.

The largest observed process-tree RSS across the corrected cohort is 25,649,152 bytes; the longest whole-child wall is 42.97 ms, including reference verification.
These single feasibility samples stayed within the declared caps. The shared
workstation was not isolated: the lock reports one-minute load 2.15 and other
work existed earlier; the coordinated GCD builds had finished before this
corrected campaign. No comparative timing, crossover or scaling claim follows.

**Decision: continue to a separate production design proposal; do not ship this
prototype as a scheduler.** The narrow go gate is met by four independently
verified recoveries under unchanged limits, finite retries and the transactional
criterion argument. A production proposal must remove the duplicate successful
build, define reversible queue bookkeeping without a full snapshot, expose or
bound owned capacities, preserve deadlines and prove that every unresolved pair
remains reachable. It must compare total time/RSS against static 1 and other
caps on larger public workloads before claiming an adaptive advantage. There is
no production-default change, broad memory guarantee or generic performance
claim in this PR.

[`corrected/cohort.json.gz`](../../research/batch-splitting/corrected/cohort.json.gz)
contains every exact stdout/stderr and all full answers, metadata and outcomes;
[`environment.json`](../../research/batch-splitting/corrected/environment.json)
adds build/configuration and both Singular wrapper/ELF hashes. The binary was
built from the identical Rust source at `b8a9bc2b`; only the Python runner,
diagnostics and documentation changed at the corrected instrument commit.
[`benchlock.txt`](../../research/batch-splitting/corrected/benchlock.txt) and
[`run-command.sh`](../../research/batch-splitting/corrected/run-command.sh) retain
actual lock events and the exact historical command. Replay uses fresh scratch
and output paths as described above.
