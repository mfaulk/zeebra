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
cargo build --release --features research-work --example symbolic_attribution
tools/benchlock.sh symbolic-742 timeout --signal=INT --kill-after=60s 600 \
  taskset -c 4 "$CARGO_TARGET_DIR/release/examples/symbolic_attribution" > research/symbolic-attribution/replay.tsv
```

The six arms are first-applicable (baseline), unique pair multiples (`dedup`),
first-applicable among minimal leading monomials (`active`), both filters
(`active-dedup`), last-applicable (`newest`), and fewest terms with an earlier-index
tie break (`sparse`). `excluded` counts elements removed from the reducer search,
not from the frozen basis or pair seeds. Equal leads keep the earlier element.

Forward counts use the production structured Adaptive elimination and passive
`research-work` counters. They exclude back-substitution and final interreduction.
These are frozen-batch ablations, not alternative complete F4 runs or timings.
The active filter is a divisibility control, not an emulation of msolve's
history-dependent redundancy flags (which also test polynomial degree).
