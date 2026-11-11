# Classify before direct lex elimination (#417)

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
