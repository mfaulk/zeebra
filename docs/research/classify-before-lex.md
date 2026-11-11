# Classify before direct lex elimination (#417)

**Measured at:** `78172295`, based on `ffdb08fd`; raw records retain the delta patch id.

`SolvePolicy::ClassifyThenDirectLex` is an opt-in M27 route-selection policy. It computes a
complete grevlex basis and classifies its leading ideal before starting direct lex F4. A
positive-dimensional ideal is refused at that point. A finite ideal proceeds to lex, without
conversion or a second dimension diagnosis. An incomplete grevlex run remains inconclusive.

The policy pays for an extra basis on finite systems. It does not replace either explicit
strategy or the default planner policy. Both F4 computations share the smaller of the attempt
batch limit and the remaining shared batch limit. Matrix limits and F4 wall-clock limits remain
per computation; the plan's elapsed limit gates attempts, not stages within an attempt.

The grevlex basis is dropped before lex starts. The plan retains its counters in
`statistics.diagnosis`, and the direct lex counters in `statistics.f4`. Batches add and peak
estimates take the maximum. The text report labels the first stage `Preclassification`.

## Comparison protocol

The runner uses the existing planted, katsura and cyclic generators, with seed 417 and the same
1000-row/1000-column matrix budgets for both policies. These limits bound the positive-dimensional
lex refusal and match the regression fixture inherited from #376. Other F4 limits remain at
their defaults. This is a policy comparison under those limits, not an unrestricted F4 benchmark.

Build from the repository root, so `.cargo/config.toml` applies:

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-417
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
mkdir -p "$TMPDIR"
cargo build --release --example classify_before_lex
export ZEEBRA_MACHINE=fedora
export ZEEBRA_AFFINITY=2
tools/benchlock.sh 417-classify timeout --signal=INT --kill-after=10s 120 \
  taskset -c 2 "$CARGO_TARGET_DIR/release/examples/classify_before_lex" \
  katsura-6-minus-one classify
```

Replace the final two arguments with each combination of `planted-8`, `katsura-5`,
`katsura-6-minus-one`, `cyclic-4-gf2` and `direct`, `classify`. Run each row in a fresh process to
attribute process peak RSS. Repeat each combination and retain every JSON record. Records carry
the commit, merge base, patch id, machine, affinity, full plan, verified-point status, outcome,
elapsed time, batch count and peak RSS. Machine and affinity values must describe the actual run.

The two positive-dimensional fixtures include the characteristic-two cyclic system **without
field equations**. No inference about finite Boolean varieties or cryptanalytic frontier size
follows from their refusal. A point returned on a finite fixture is independently evaluated against
every original generator. Absence of a point and an inconsistent ideal remain distinct outcomes.

## Measured comparison scoreboard

Measured 2026-11-11 on `fedora`, AMD Ryzen Threadripper PRO 5995WX, one worker pinned to logical
CPU 2. Release, x86-64-v3, fat LTO, one codegen unit. The machine-wide benchmark lock covered the
whole sweep; its START/END load averages were 1.48 and `end=exited status=0`. Five fresh-process
runs per combination, alternating policy order between repetitions. Every returned point was
verified against the original generators. All positive-dimensional refusals agreed across policies.

[All 40 records](../../research/classify-before-lex/runs.json) retain nanosecond timings, process
peak RSS, batch counts, the environment and the text plan. The scoreboard below reports medians
and the full observed timing ranges; MB means decimal MB. Direct includes any post-failure grevlex
diagnosis, so the comparison charges the complete cost of reaching the same answer.

| Input | Policy | Time: median [min, max] | Process peak RSS: median | Total batches | Outcome |
|---|---|---|---|---:|---|
| planted-8 | direct | 0.503 ms [0.439, 0.704] | 3.543 MB | 2 | verified point |
| planted-8 | classify | 0.540 ms [0.469, 0.549] | 3.662 MB | 4 | verified point |
| katsura-5 | direct | 0.861 ms [0.755, 0.939] | 4.219 MB | 20 | verified point |
| katsura-5 | classify | 1.365 ms [1.094, 1.440] | 4.248 MB | 25 | verified point |
| katsura-6-minus-one | direct | 12.313 ms [11.984, 12.545] | 5.345 MB | 16 | positive-dimensional |
| katsura-6-minus-one | classify | 1.335 ms [1.223, 1.633] | 4.461 MB | 5 | positive-dimensional |
| cyclic-4 over GF(2) | direct | 0.111 ms [0.107, 0.157] | 3.555 MB | 8 | positive-dimensional |
| cyclic-4 over GF(2) | classify | 0.102 ms [0.087, 0.142] | 3.596 MB | 6 | positive-dimensional |

The positive-dimensional katsura fixture saves the entire failed lex computation: 11 batches,
with the same five-batch grevlex classification on both policies. The median refusal is 9.22x
faster at these limits. Solvable katsura-5 instead takes 1.59x as long and spends five extra
batches. Planted-8 doubles its batch count, but its timing ranges overlap; no runtime win or loss
is established there. The GF(2) ranges also overlap, despite two fewer batches. Process RSS is
reported separately from the plan's estimates and includes startup, generators and allocator costs.
These tiny rows do not support a general memory-scaling claim.

**Decision:** retain the policy as an explicit option for callers who want dimension classification
before lex elimination. Keep the defaults. The benefit is a cheaper refusal on an ideal the solver
cannot use; the cost is an extra basis on finite ideals. These measurements do not select a new
automatic route, close #273's broader objective-selection work, or extend a cryptanalytic frontier.

To reproduce the repetitions, run each of the four input names five times with each policy under
the lock command above, using `direct` then `classify` on odd repetitions and the reverse on even
ones. Each invocation is a fresh process. Take medians from `record.elapsed_nanos` and
`record.measured_peak_resident_bytes`; `repeat` in the retained array identifies the repetition.
