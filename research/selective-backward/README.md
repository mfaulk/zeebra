# Selective F4 backward reduction (#269)

This is an opt-in research experiment. The production full-RREF path remains the control.
The prototype keeps forward pivots/arithmetic/scheduling fixed and uses one generic dense
row to clear later echelon pivots from selected targets, left to right. It never discards
an inherited pivot before a candidate has used it. No public RREF contract changes.

Predeclared gate: five interleaved fresh-process repetitions at both 32003 and 2147483647,
one worker, CPU 3, release/fat LTO/one codegen unit/x86-64-v3. Initial MQ10 arms are stock,
observed full sparse back-substitution, dense all targets and dense candidate targets.
The last two separate row-major materialization from target selection. Work-on repeats
are separate from native timings. Build and test before taking `tools/benchlock.sh`.
Use the existing 60-second/2-GiB child and 185-second parent guards and unchanged F4 limits;
every failure/refusal stays in the artifacts. No build may overlap measurement.

Acceptance: all completed answers must match the existing complete independently checked
reduced bases and input digests. For further consideration, selected reduction must improve
MQ10 complete F4 median by at least 10% at both primes, use at most 1.25x peak RSS, and not
regress Cyclic-5 or Katsura-6 complete medians by more than 5%. Five repetitions establish
only a bounded feasibility verdict, not a production shipping decision. Any apparent win
also gets the existing MQ14 60-second fixed-budget probe; stops are not speedups.
No repeated extension is planned if noise obscures the sign. A later production proposal
requires its own review. Parallel-forward crossing follows the isolated verdict and does
not change this experiment's serial forward schedule.

The correctness argument, exact commands, retained attempts and scoped decision are recorded
in `docs/research/elimination-kernels.md`. H2 marked scanning is a separate factor: no scan
heuristic is bundled into this prototype.

## Reproduce

For the recorded serial campaign, create a checkout at controller `c148058b`; its Rust/Cargo
files are byte-identical to the `0ed4fe33` build pin. Use rustc 1.99.1 as recorded. The commands
below rerun the protocol in that checkout; run offline artifact validation in the PR checkout,
which contains the later summary tools. The recorded host uses mold; incremental caching
was enabled for both builds. The explicit flags below pin that setup rather than inheriting
a user override. Keep separate build directories for the serial and
combined revisions.

```sh
git worktree add ../zeebra-269-serial-repro c148058b
cd ../zeebra-269-serial-repro
```

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-269
export RUSTC_WRAPPER=''
export CARGO_INCREMENTAL=1
export RUSTFLAGS='-C target-cpu=x86-64-v3 -C link-arg=-fuse-ld=mold'
export TMPDIR="$CARGO_TARGET_DIR/tmp"
mkdir -p "$TMPDIR" "$CARGO_TARGET_DIR/frozen"
cargo test --features research-work --lib linalg::selective
cargo test --features research-work --example mq10_profile
python3 tools/test/selective-backward-study-test.py
cargo build --release --example mq10_profile
cp "$CARGO_TARGET_DIR/release/examples/mq10_profile" "$CARGO_TARGET_DIR/frozen/stock"
cargo build --release --features research-work --example mq10_profile
cp "$CARGO_TARGET_DIR/release/examples/mq10_profile" "$CARGO_TARGET_DIR/frozen/observed"
```

Commit the instruments before measuring. With matching machine identity and actual affinity:

```sh
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=3 \
  tools/benchlock.sh selective-backward-269 taskset -c 3 \
  python3 tools/external/selective-backward-study.py \
  --stock "$CARGO_TARGET_DIR/frozen/stock" --binary "$CARGO_TARGET_DIR/frozen/observed" \
  --build-commit "$(git rev-parse HEAD)" \
  --scratch "$CARGO_TARGET_DIR/native" --output "$CARGO_TARGET_DIR/native.json.gz"
```

Use separate outputs and scratch directories with `--phase work` for passive-work overhead
controls, or `--phase probe` for the larger MQ14 fixed-budget probe. `--resume` only continues
a verified prefix stopped by an ambient-load or compiler gate, with unchanged source, binaries
and limits. The runner checks for compiler processes before and after every child. One attempt
interrupted by new ambient compilation may be retained separately and retried after the gate
clears; a second such interruption ends this bounded confirmation without an adoption verdict.
The work cohort has five fresh processes each for full-off, full-on, dense-all-on and
selected-on, separately from the 120 native attempts. It checks every complete coefficient
and the complete F4 pair/degree/shape trajectory. Source inputs remain the existing public
corpus; independent reference files are hashed into every cohort.

The research entry charges the retained original target plus the live dense copy against the
existing live-entry allowance, so it can refuse earlier than the ordinary algorithm. It separately
bounds dense cells plus the column index to 64 MiB. Reported sparse capacities include the
output buffer before replacement. They exclude allocator metadata, observer masks, thread
stacks and source polynomials; process RSS includes the whole child. Two scratch/index
allocations plus one output allocation per nonzero selected target replace repeated sparse
merge/copyback operations. No buffer capacity is transferred between target rows.

Decode packed answers with `tools/external/study_artifacts.py`'s `load_study` or `iter_attempts`.
The content-addressed payload hashes are checked during decoding. Native whole-process wall,
self peak RSS and F4 stages are separate quantities; work-on and probe times are not native
performance samples. Logical field products and scanned cells are not physical DRAM bandwidth.


The first 160-attempt cohort at `0ed4fe33` completed all coefficient checks, but compilation
started in another worktree during its measurement window. Its times are excluded from the
performance decision and retained under `exploratory/`. A single bounded confirmation uses
the same four arms, five accepted repetitions and acceptance thresholds, adding compiler gates.
The frozen Rust sources/executables remain at `0ed4fe33`; the controller records its own commit
separately and rejects a changed Rust source tree. Environmental gate waits are not new samples.


## Forward/backward crossing (declared before running)

After the serial gate passes, `cross.py` runs five fresh-process repetitions per family/field
of serial full, serial selected, four-worker full and four-worker selected. MQ10 additionally
gets same-algorithm one-worker full/selected controls: 140 native attempts total. A separate
12-attempt work phase has one diagnostic per MQ10 field/arm, never pooled with native times.
Serial and one-worker children pin CPU 3; four-worker children pin CPUs 0–3. The same compiler,
load, 60-second/2-GiB guards and original F4 budgets apply. No repeated extension is planned.
Acceptance of the serial gate does not imply that the parallel combination wins; report it
separately against both serial selected and one-worker selected. No production defaults change.

The four MQ14 probes are serial full/selected at both primes, one attempt each at the same
60-second/2-GiB cap. A completed probe needs an independent reference before it is timing
or capacity evidence. Refusals remain visible; no speedup is inferred from them.

Use a separate checkout at controller `4c39c1bc` for the combined campaign; its Rust tree matches
`ff15a0af`. Build that example with `cargo build --release --features research-work --example mq10_profile`
after its tests pass, and freeze it separately from the original serial-cohort executable.
Then run (using separate scratch/output names for `--phase work` and `--phase probe`):

```sh
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=0,1,2,3 \
  tools/benchlock.sh selective-backward-269-cross taskset -c 0-3 \
  python3 research/selective-backward/cross.py \
  --binary "$CARGO_TARGET_DIR/frozen/combined" \
  --scratch "$CARGO_TARGET_DIR/cross" --output "$CARGO_TARGET_DIR/cross.json.gz"
```

Offline validation rechecks complete bases, trajectory and compiler boundaries, source/binary
identities and the SHA256 inventory, then regenerates `summary.json` and `native.csv`:

```sh
python3 tools/test/selective-backward-study-test.py
python3 tools/test/selective-backward-summary-test.py
python3 tools/test/selective-backward-cross-test.py
python3 research/selective-backward/summarize.py
```

The combined executable's Rust source pin is `ff15a0af`. The controller records its own
revision separately and rejects a different Cargo/library/example tree. Resume accepts
retained resource-limited probe outcomes without reclassifying them as verified answers;
failed or unverified native timing attempts still cannot resume.


## Retained result

The isolated serial gate passes, and the four-worker combination improves MQ10 further,
but scoped parallel dispatch regresses the small classical controls. All four MQ14 probes
stop at the existing 32-million-entry budget. No production default or frontier-capacity
claim follows from these experiments. See the report's separate adopt/reject/defer decisions.

`native.json.gz`/`work.json.gz` retain the 160 accepted serial attempts;
`cross-native.json.gz`/`cross-work.json.gz` retain 140 native crossings and 12 diagnostics;
`probes.json.gz` retains four resource refusals. `exploratory/` retains 160 earlier complete
answers whose times are excluded. The source/controller pins travel in each cohort.
`benchlock.log` and `cross-benchlock.log` preserve the complete lock windows, including the
1,737-second queue wait. Every archive/payload/log is covered by `inventory.json`.

The combined executable also echoes the full ordered generators after the self-RSS snapshot;
whole-process timing includes that output, while the F4 timer excludes parsing/rendering.
Its samples therefore stay in their own cohort. Recheck the crossing with:

```sh
python3 tools/test/selective-backward-combined-summary-test.py
python3 research/selective-backward/combined_summary.py
```

`combined-summary.json` retains native spreads, all F4 stages, worker-local diagnostics and
explicitly unverified probe outcomes. It checks direct/passive worker products and complete
row aggregation. Conservative concurrent reservations are not mathematical nonzero peaks.

Production integration is tracked separately in [#749](https://github.com/mfaulk/zeebra/issues/749).
The measured prototype remains opt-in pending that contract/budget review.

The crossing controller at `4c39c1bc` is byte-identical to the measured `1bf48baa` controller;
the latter adds the exploratory-data audit and documentation. Both have the same frozen Rust
tree as `ff15a0af`. The serial `0ed4fe33`/`c148058b` Rust/Cargo trees are likewise identical.
