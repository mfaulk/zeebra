# Strategy selection: what the planner optimizes, measured (#273)

**Measured at:** `ea3af415` (the first commit of #273, based on `8dbf9bcf`; the binary was
built from that tree). One run, 2026-11-15, under `tools/benchlock.sh` (tag `zb-273`, `START
load=22.31`, `END load=10.46`, 62 s), pinned with `taskset -c 4`, `--release` (fat LTO,
`x86-64-v3`), rustc 1.99.1. The ambient load was high: read ratios, not absolute times.

The issue asked for three things: a planner that can be told whether time or memory matters, a
measured table of which route wins where, and the classical-versus-sparse-FGLM crossover. This
document reports all three, and the third is **not measured** (§5).

## 1. What was added

`PlannedSolveOptions::objective: PlanObjective`, consumed by `solve_one_planned`. Nothing else in the
solver changes, and `Time` is the default, so existing callers behave as before.

| objective | what the planner does differently |
|---|---|
| `Time` | nothing — the policy's routes under the caller's `F4Options` |
| `PeakMemory` | every F4 batch capped at `MEMORY_PAIR_CAP = 16` pairs (or the caller's tighter cap) |
| `CompletionWithinBudget` | as `Time`; a route refused by a **matrix** limit (rows, columns, live entries, live bytes) is attempted once more under the cap, from the shared budget, before any fallback |

`SolvePolicy::Explicit` ignores the objective. A batch or wall-time refusal is not retried under the
cap: capping only adds batches. Each `Attempt` records `pair_cap`, the plan's log prints
`Objective: …` and `F4 batches capped at 16 pairs`, and a capped re-attempt is
`Choice::ReattemptUnderPairCap { limit }`, naming the `F4Options` field the first attempt crossed.

**Why a fixed cap rather than the Hilbert cap.** `hilbert-driven.md` §2–§4 measured both. The Hilbert
prediction underestimates by 39% to 46x on the inhomogeneous systems, so its slack has to be tuned
per instance; a fixed cap of 16 reached nearly the same peak with no prediction (52 447 against
50 274 peak entries on Poseidon `t=2 R_F=2 R_P=2`). The issue's acceptance rule — no route chosen on
a prediction whose error has not been measured — rules the predicted cap out as a default and leaves
the fixed one, whose cost is measured.

**Why 16.** It is the one fixed cap `hilbert-driven.md` measured on both of its instances, and it is
the configuration behind the clearest measured time/memory divergence in the repository (§3). No
sweep over cap values was run here.

## 2. The route table

```sh
tools/benchlock.sh <tag> taskset -c 4 \
    "$CARGO_TARGET_DIR/release/examples/strategy_selection" 5
```

Ten instances from six families over GF(2^31 − 1), four routes each, five repetitions interleaved
(every route once per repetition, arm order rotated). Every F4 computation runs under a 2 s
`max_wall_time`, so a route that cannot finish is a bounded refusal. Peak is
`SolvePlan::peak_estimated_bytes` — the larger of F4's matrix estimate and FGLM's dense blocks — not
RSS. Every returned point is verified against the generators.

The four routes are grevlex F4 then FGLM (**G**), direct lex F4 (**L**), and each under the 16-pair
cap (**G/c**, **L/c**). Times are the median in ms; `—` is a refusal at the 2 s budget.

| instance | ρ | `D` | G | L | G/c | L/c | peak G | peak L | peak G/c |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| katsura-5 | 0.90 | 16 | 0.526 | 0.641 | 0.433 | 0.551 | 13 408 | **8 163** | 13 408 |
| katsura-6 | 0.93 | 32 | **1.218** | 4.311 | 1.262 | 4.294 | **55 280** | 68 251 | 55 280 |
| cyclic-5 | 1.00 | 70 | 0.982 | **0.914** | 0.984 | 0.913 | 120 320 | **18 238** | 120 320 |
| eco-6 | 1.00 | 16 | **0.631** | 1.949 | 0.633 | 1.948 | 17 273 | 39 088 | **15 557** |
| eco-7 | 1.00 | 32 | **2.342** | — | 4.970 | — | 75 595 | 10 618 531 | **59 128** |
| noon-4 | 1.00 | 73 | **1.140** | — | 1.131 | — | **117 648** | 12 516 740 | 117 648 |
| noon-5 | 1.00 | 233 | **12.083** | — | 13.478 | — | **1 088 304** | 33 938 209 | 1 088 304 |
| reimer-4 | 0.00 | 36 | **0.878** | 12.941 | 0.925 | 13.053 | **47 024** | 130 804 | 47 024 |
| planted-8 | 0.14 | 256 | 2.323 | **0.251** | 2.429 | 0.256 | 1 128 448 | **1 373** | 1 128 448 |
| planted-10 | 0.11 | 1 024 | 21.023 | **0.278** | 20.760 | 0.278 | 17 174 528 | **1 706** | 17 174 528 |

ρ is `SystemShape::interaction_density`. Peak for **L/c** equals **L** on every row and is omitted;
for the refused lex rows it is the peak reached before the refusal. Per-repetition minimum and
maximum, and batch counts, are in the example's output.

### 2.1 Route versus route, with the margin

The capped and uncapped forms of one route are not different routes on most rows: the cap binds only
where a degree offers more than 16 pairs. So the margins below are **G-family against L-family**,
each family's best median, with "within noise" when the faster family's slowest repetition is not
faster than the slower family's fastest.

| instance | time winner | margin | memory winner | margin | planner under `Time` | right? |
|---|---|---:|---|---:|---|---|
| katsura-5 | G | 1.27x | **L** | 1.64x | G | within noise (ranges overlap) |
| katsura-6 | G | 3.5x | G | 1.23x | G | yes |
| cyclic-5 | **L** | 1.08x | **L** | 6.6x | G | **no, by 1.08x** — outside this run's range, small |
| eco-6 | G | 3.1x | G/c | 1.11x over G | G | yes |
| eco-7 | G | L refused | G/c | 1.28x over G | G | yes |
| noon-4 | G | L refused | G | 106x | G | yes |
| noon-5 | G | L refused | G | 31x | G | yes |
| reimer-4 | G | 14.7x | G | 2.8x | G | yes |
| planted-8 | **L** | **9.3x** | **L** | 822x | G | **no, by 9.3x** |
| planted-10 | **L** | **75x** | **L** | 10 067x | G | **no, by 75x** |

**`Time` picks the winner on seven of ten rows**, within noise on one, and loses on three: cyclic-5
by a small margin and the planted family by 9x and 75x. The planted loss is the 70x spread #273's
thread already recorded, reproduced. Under `AutoWithFallback` planted-12 is still rescued by the
counted-`D` refusal (`Choice::ConversionRuledOut`); planted-8 and planted-10 fit the conversion
budget, so nothing rescues them.

### 2.2 No cheap feature in this table separates the planted family, and none is adopted

A rule that sent planted to direct lex would need a feature computable before the route runs. The two
candidates the table offers both fail on it:

- **Interaction density.** planted is 0.11–0.14 and every row where lex loses is ≥ 0.90 — except
  **reimer-4 at 0.00, where lex loses by 14.7x**. A density threshold would send reimer the wrong way.
- **Quotient dimension**, which is not even pre-basis: **noon-5 at `D = 233` refuses direct lex at
  the 2 s budget, while planted-8 at `D = 256` finishes it 9.3x faster than conversion.** Neighbouring
  `D`, opposite winners, margins of two orders of magnitude. `D` does not predict the route.

A rule fitted to ten rows and validated on the same ten is not a measured prediction, so the `Time`
objective keeps the conservative opening and its losses are recorded here rather than tuned away.
The planted generators are pairwise-coupled blocks; a block-decomposition test (connected components
of the variable-interaction graph) is the feature this table suggests next, and it is a hypothesis
until measured on a family other than planted.

## 3. Time-optimal and memory-optimal differ — the case for the parameter

In §2 the memory objective's cap is a strict win on memory on two rows (eco-6 11%, eco-7 28%) and a
no-op elsewhere, because on katsura, noon, reimer, cyclic and planted the peak is FGLM's dense blocks
(`D² + D(D+1)` cells), which a pair cap cannot touch. Its time cost here is inside the noise: eco-7
G/c's median is 2.1x G's, but the ranges overlap (2.25–4.16 against 2.63–6.49 ms).

The decisive divergence is the cap-16 configuration in `hilbert-driven.md`, on the same F4 options:

| instance | configuration | peak entries | solve ms |
|---|---|---:|---:|
| Poseidon `t=2 R_F=2 R_P=2` | uncapped | 103 112 | **142.2** |
| | fixed cap 16 | **52 447** | 168.5 |
| Fukuoka III `n=10` | uncapped | 168 020 | 118.6 |
| | fixed cap 16 | **48 755** | **37.9** |

On Poseidon the time optimum is uncapped and the memory optimum is capped — 49% fewer peak entries
for 1.18x the time. On Fukuoka the cap wins both. **One flag, two objectives, opposite answers on
one instance** is what a planner without an objective cannot express, and what
`test_time_and_memory_objectives_choose_differently` pins: on eco-6 the memory objective runs
strictly smaller F4 matrices than the time objective, with the same answer.

**Memory is where the objective most often picks the wrong route**, and that is recorded rather than
fixed: on katsura-5, cyclic-5 and the planted rows **direct lex** has the smallest peak (1.6x to
10 067x), and `PeakMemory` keeps the grevlex opening. Sending a memory-bound caller to direct lex
would be wrong on eco-7, noon-4 and noon-5, where lex reaches 10–34 MB before refusing against
G's 0.06–1.1 MB. The same feature problem as §2.2 blocks a rule.

## 4. Completion within a budget

A matrix-limit refusal is the case the cap can turn into an answer. `test_completion_retries_a_matrix_refusal_under_the_cap`
sets katsura-6's live-entry limit to exactly the capped run's peak: `Time` is refused, and
`CompletionWithinBudget` answers on the capped second attempt of the same route. The existing
measurement that says this is not an artificial case is `hilbert-driven.md` §4, Poseidon
`t=2 R_F=4 R_P=0`: 237 265 peak entries uncapped against 94 621 at cap 64 in the same time — a
budget between the two refuses the default and admits the cap. Cap 16 was not measured on that
instance. **The cost of a refusal-then-retry, as opposed to running capped from the start, is not
measured here**; it is at most the refused attempt's elapsed time, which the plan reports as
`discarded_elapsed`.

## 5. Not measured

- **The classical-versus-sparse-FGLM crossover.** The planner has no sparse conversion to choose:
  `SolveStrategy` offers `DirectLexF4` and `GrevlexF4ThenFglm` only, and the Wiedemann and Krylov
  conversions are reachable as library functions, not as planner routes. Wiring one in is #224's
  territory (and the `fglm` module is being changed concurrently), so this document invents no
  crossover. The conversion-level comparisons that exist are in `order-conversion.md` (the Krylov
  shape route at 0.37x on the route at `D = 64`) and `wiedemann-krylov.md`; the stage crossover from
  border reduction to the dependence walk falls between `D = 64` and `D = 156` (`order-conversion.md`).
- **Whether msolve or Sagebrush select routes internally.** Not examined; H8 and H10 own that.
- **The field-size-aware density predicate** handed over from #441 (`(1 − 1/q) · m`). Every row here is
  one field, so a field-dependent feature has nothing to vary against.
- **RSS.** Peaks are the planner's payload estimates. `SolveStatistics::estimated_peak_bytes` explains
  why they differ from resident memory.

## 6. Reproducing

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-273 RUSTC_WRAPPER=""
cargo build --release --example strategy_selection
tools/benchlock.sh <tag> taskset -c 4 "$CARGO_TARGET_DIR/release/examples/strategy_selection" 5
cargo test --lib planning
```

About a minute. An exploratory single-repetition run in the `ci-release` profile showed noon-4's
capped route 4.4x faster than the uncapped one; five interleaved repetitions put the two at 1.01x.
That is why every margin above carries its range.
