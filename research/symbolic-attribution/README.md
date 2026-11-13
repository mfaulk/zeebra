# Symbolic preprocessing attribution (#742)

`examples/symbolic_attribution.rs` replays every batch of the digest-pinned
`mq-random-10` at GF(32003). Every arm uses the baseline's basis and pairs.
The baseline replay asserts exact equality with production symbolic preprocessing
(rows, monomial order, term handles and covered leads). Duplicate seed removal
also asserts an identical column set. No library behavior changes.

Build and run from the repository root:

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-742 RUSTC_WRAPPER=""
cargo test --features research-work --example symbolic_attribution
cargo clippy --features research-work --example symbolic_attribution --tests -- -D warnings
cargo build --release --features research-work --example symbolic_attribution
tools/benchlock.sh symbolic-742 timeout --signal=INT --kill-after=60s 600 \
  taskset -c 4 "$CARGO_TARGET_DIR/release/examples/symbolic_attribution" > research/symbolic-attribution/replay.tsv
```

The arms are first-applicable (baseline), unique pair multiples (`dedup`),
first-applicable among minimal leading monomials (`active`), both filters
(`active-dedup`), last-applicable (`newest`), and fewest terms with an earlier-index
tie break (`sparse`), and increasing initial-generator leading monomial order
(`input-order`), alone and combined with the filters. Only the original input
prefix is reordered; appended elements retain Zeebra order. `excluded` counts elements removed from the reducer search,
not from the frozen basis or pair seeds. Equal leads keep the earlier element.

Forward counts use the production structured Adaptive elimination and passive
`research-work` counters. They exclude back-substitution and final interreduction.
These are frozen-batch ablations, not alternative complete F4 runs or timings.
The active filter is a divisibility control, not an emulation of msolve's
history-dependent redundancy flags (which also test polynomial degree).

`--sorted-input` reruns the complete F4 computation with only the input generators
sorted by increasing leading monomial. It asserts exact equality of the reduced
basis with the original input order, then emits baseline and deduplicated frozen
replays of the sorted run. Save it separately as `sorted.tsv`. The corpus digest
continues to identify the original published system. The library and its pair
criteria are unchanged.

`python3 research/symbolic-attribution/summarize.py` checks the retained campaign
against #737 and prints totals. CI runs this check and the instrument's unit tests;
CI does not rerun the measurement campaign or require msolve.

Retained files:

- `replay.tsv`: nine controls on the original ten frozen batches, at `575f59d9`.
- `sorted.tsv`: the full sorted-input run's baseline and deduplicated replays, at `f80adee9`.
- `totals.tsv`: output of the summarizer.
- `metadata.json`: base commit, instrument/code-delta hashes and raw-record hashes.
- `benchlock.log`: the two completed measurement windows; no timing claim is made.

The [report](../../docs/research/symbolic-attribution.md) contains the per-round
attribution and the remaining cross-engine uncertainty. Reproduce the sorted run
with the same pinned command plus `--sorted-input`, writing to `sorted.tsv`.
The final instrument adds a mode header to `replay.tsv`; count records match the
retained earlier instrument exactly.
