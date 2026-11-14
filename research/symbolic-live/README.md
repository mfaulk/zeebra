# Live symbolic policy pilot (#753)

The opt-in `research-work` policy keeps basis indices and pair seeds in their original order.
`mq10_profile --symbolic=order` sorts only the normalized distinct initial generator prefix in
first-applicable reducer searches; later inserted basis elements retain insertion order.
`--symbolic=dedup` retains one seed for each exact `(basis_index, monomial_multiplier)` identity;
`--symbolic=both` combines them. `--symbolic=original` observes the original policy with a scope;
omitting the flag leaves the scope inactive. The feature-absent binary is an additional control.
Ordinary F4 defaults and public full RREF are unchanged.

A duplicate seed is the exact same monic polynomial multiple. Its retained occurrence is enough
to express every original S-relation, and pair LCMs stay covered. Distinct basis identities with
equal leads or proportional polynomials are not collapsed. No coefficient test or new field API
is introduced. Closure rows and extraction use existing code; final interreduction does not use
the experimental ordering. Reduced row counts can admit a system under the same row allowance;
limits are not raised or redefined. The seed-key table and sorted index vector cost additional
scratch; reported capacities model entries, not allocator bytes or RSS.

## Predeclared bounded plan

Freeze and commit the instrument before building. Use release/fat LTO/one codegen unit with the
repository's x86-64-v3 ISA and system allocator; private build/scratch under `/buildcache`, empty
`RUSTC_WRAPPER`, `CARGO_INCREMENTAL=0`, at most 16 concurrent compiler jobs. Build a feature-absent
stock and a feature-present experiment, copy each executable before rebuilding the next arm.

Exactly one bounded 2×2 policy experiment, no speculative follow-up retries:

- Native: 5 interleaved fresh-process repetitions × 9 field/input cells × 6 arms = 270 attempts.
  Arms are stock, feature-present/scope-off, original-scope, order, dedup, combined. Stage clocks
  are on, coefficient instrumentation is off; every cost of policy preparation remains inside F4.
- Work diagnostics: 1 separate deterministic observation × 9 cells × 4 scoped policies = 36.
  Work observations are not pooled into timing medians and are not repeated timing evidence.
- Stage-off: 5 interleaved repetitions × the two MQ10 fields × 4 scoped policies = 40.

Cells are MQ10, Cyclic-5 and Katsura-6 at 32003/2147483647, plus public Eco-4, Noonburg-3 and
Reimer-3 at their only pinned field 32003. References bind original ordered generators and
complete reduced bases, independently checked against retained Singular answers. Public smoke
controls are small-case correctness/regression evidence, not broad performance claims.

Each attempt has the existing 60-second/2-GiB descendant RSS guard and 185-second outer watchdog.
The runner stops starting work at 900 seconds aggregate wall or 512 MiB scratch output. Absolute
aggregate wall including a final admitted child is at most 960 seconds plus checking/writing;
the mathematical sum of per-child caps is 20,760 seconds, so the aggregate gate is binding.
Expected native execution is under five minutes; this is an estimate, not a result. Retain every
attempt/refusal, no solver retry or budget escalation. Compiler/load gates (maximum 1-minute load4)
and `tools/benchlock.sh` serialize measurement; all builds/tests finish before locking. The root
agent also coordinates with the separate #751 campaign so no sibling compiles during measurement.

Adoption requires at least 10% reduction in named complete-process and complete-F4 median wall,
no more than 5% material small-control regression, and at most 1.25× maximum RSS, with matched
same-session controls and independent complete answers. Sub-millisecond controls cannot establish
precise 5% performance ordering; overlapping ranges are inconclusive. A process gain that only
changes output/rendering is insufficient. At most one 2×2 is run; retain reject/defer if gates fail.
Post-#749 serial candidate reduction is always used; no backward/concurrency factor is bundled.

## Reproduction

```sh
export RUSTC_WRAPPER=''
export CARGO_INCREMENTAL=0
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-753
export TMPDIR="$CARGO_TARGET_DIR/tmp"
mkdir -p "$TMPDIR"
cargo test -j16 --features research-work --test symbolic_live
cargo test -j16 --features research-work --example mq10_profile
python3 tools/test/symbolic-live-study-test.py
cargo build -j16 --release --example mq10_profile
cp "$CARGO_TARGET_DIR/release/examples/mq10_profile" "$CARGO_TARGET_DIR/stock"
cargo build -j16 --release --features research-work --example mq10_profile
cp "$CARGO_TARGET_DIR/release/examples/mq10_profile" "$CARGO_TARGET_DIR/observed"
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=4 \
  tools/benchlock.sh symbolic-live-753 taskset -c 4 \
  python3 tools/external/symbolic-live-study.py \
    --stock "$CARGO_TARGET_DIR/stock" --binary "$CARGO_TARGET_DIR/observed" \
    --scratch "$CARGO_TARGET_DIR/campaign" --output research/symbolic-live/results.json.gz
python3 tools/external/symbolic-live-study.py --replay research/symbolic-live
```

The executable JSON additionally records exact scope/seed capacities, full stages, mathematical
entry peaks, production reservations and complete coefficient basis. Work diagnostics retain
per-batch dimensions, actual coefficient products and modeled traffic; these are not physical
memory bandwidth. Process wall/CPU/RSS include original input and full answer encoding; independent
reference checking is outside that timed child. Publication records source, executable, toolchain,
lockfile, actual topology/affinity and environmental gates. A baseline/current profile from #751
must precede any production adoption recommendation.
