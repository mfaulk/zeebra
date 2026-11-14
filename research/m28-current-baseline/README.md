# Current whole-route baseline (#751)

This bounded study extends `mq10_profile` rather than introducing a solver. Ordinary invocations
retain their complete reduced-grevlex-basis task. `--whole-route=fglm` composes shipped default
F4, default adaptive FGLM and `solve_from_lex_basis`; `--whole-route=direct` uses lex F4 then the
same recovery. These are explicit fixed routes, not a planner decision or all-point enumeration.

Predeclared pilot: six fresh processes, MQ10 and Cyclic-5 conversion routes at both published
small primes, the historical weak Katsura-11 reduced-grevlex-basis identity at GF(2147483647),
and a direct-lex MQ10 control at GF(32003). Each child is capped at 60 seconds and 2 GiB with
the existing descendant guard and nested 185-second watchdog. Six solver caps total at most 360 seconds;
the pilot has a 480-second aggregate outer watchdog and 256 MiB output budget. The exact independent Singular answer is reused from #739’s
`research/comparand-scaling/singular-reference31-v1.json.gz`; its archive hash, full source/checker
identity and exact coefficient-set verification are retained in the cohort. The archive SHA-256 is
`d52ca65cbdc2a088e42da3faeb58305cbfa614dc2e6740de09fd2b6d13c133c1`. No new oracle is run.
The exact frozen Katsura digest is `03bf44d5d614a21cc8f56462aa873b7961641a2341892e3b2ef52b6cfec86a13`. No retry or
larger allowance is authorized. Compiler/load gates run before and after every child. All stops,
complete phase checkpoints and partial stdout remain retained; no partial basis is accepted.

A later native cohort requires reviewing the pilot first. Its declared grid has five alternating
stage-off/on repetitions for MQ10, Katsura-6 and Cyclic-5 at both primes; five separate work-on
MQ10 repetitions at each prime; and five staged repetitions of the weak Katsura-11 identity.
That is 75 attempts, a 900-second hard aggregate cap and the same child/output limits. The
aggregate cap overrides the 4,500-second sum of child caps; an unfinished grid remains incomplete.
The native cohort is not launched solely because this README exists.

Build and test outside the benchmark lock, using a private build/scratch path:

```sh
export RUSTC_WRAPPER=''
export CARGO_INCREMENTAL=0
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-751
export TMPDIR=$CARGO_TARGET_DIR/tmp
mkdir -p "$TMPDIR"
cargo test -j16 --features research-work --example mq10_profile --test stage_refinements
python3 tools/test/whole-route-study-test.py
cargo build -j16 --release --features research-work --example mq10_profile
```

Commit the instruments before running. Set `BUILD_COMMIT` to that source revision and use actual
physical-core affinity, then run the frozen binary under `tools/benchlock.sh`:

```sh
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=3 \
  tools/benchlock.sh m28-current-pilot-751 taskset -c 3 \
  timeout --signal=TERM --kill-after=5 480 \
  python3 tools/external/whole-route-study.py \
    --binary /buildcache/cargo-target/zeebra-751/release/examples/mq10_profile \
    --scratch /buildcache/cargo-target/zeebra-751/pilot \
    --output research/m28-current-baseline/pilot.json.gz \
    --phase pilot --build-commit "$BUILD_COMMIT"
```

Whole-route stdout consists of newline-delimited input, complete source/lex basis and active-stage
checkpoints, then a final JSON record. `whole_route_ns` includes checkpoint serialization/flush,
classification, recovery's built-in original-equation checks and an additional independent
substitution. `checkpoint_ns` measures direct checkpoint emission; it does not estimate cache or
allocator perturbation. Parsing precedes that timer and final JSON encoding follows it. Process
wall/CPU/RSS cover input, all stages and all output. Separate phase timings are never added to
parent timers twice. Stage-off/on controls quantify the passive clocks; work-on is diagnostic.

F4 forward/backward refinements describe production only. The backward boundary includes selection,
allocation, candidate finishing and any old-RREF fallback. FGLM scalar sequence/reconstruction/
certificate clocks refine dependence, including failed scalar attempts before classical fallback.
On FGLM refusal its public API returns no partial statistics, so only conversion-call wall and
last completed checkpoint are available; the report names that limitation rather than inventing
operator/certificate timings. Recovery-call wall includes the solver's own verification; the
additional original-equation substitution is timed separately.

## Retained prefix and bounded continuation

The first pilot window retained four accepted complete processes and then refused before launching
Katsura-11 because a new unrelated compiler appeared. The four accepted native responses retain
empty pre/post compiler snapshots; their one-off clocks are feasibility evidence, not repeated
performance estimates. MQ10 at GF(32003) and both Cyclic-5 inputs report no base-field point;
MQ10 at GF(2147483647) returns a point independently substituted into every original equation.
Adaptive conversion selected Classical with DenseOperator/SmallQuotient fallback respectively.
The source bases match complete independent references. `pilot.json.gz` preserves the exact
four-attempt prefix, the pre-child compiler refusal and original identities; no accepted sample
is discarded or repeated.

One controller-only continuation is declared for the two unattempted pilot cells: frozen source,
executable, reference archive, machine, affinity and toolchain must match. It writes a separate
`pilot-completed.json.gz`, retaining every original accepted attempt unchanged and the original
prefix archive SHA-256. Its two child caps total 120 seconds; an independent 180-second aggregate
watchdog and the remaining 256-MiB output budget bind. It launches only after the workstation's
compiler/load gates clear. Use `--resume-from research/m28-current-baseline/pilot.json.gz` with
`--phase pilot`, a new output path, and the same private scratch tree. This is not permission to
rerun the accepted cells or lift any solver limit.

Offline checks launch no solver and do not need the benchmark lock:

```sh
python3 tools/test/whole-route-study-test.py
python3 tools/test/whole-route-summary-test.py
python3 research/m28-current-baseline/summarize.py --check
```

The last command rechecks plan coverage or explicit interrupted-prefix status, original equations,
full source coefficients and every recovered point. Analytical ceilings use same-attempt clocks.
The existing comparand supervisor enforces process-tree wall/RSS and 128-MiB per-child output,
bounded by remaining aggregate output allowance. Launcher signals drain owned processes and retain
an interrupted attempt. Unexpected process failures are not reclassified as resource refusals.


## Reviewed native grid

The native grid is exactly 75 fresh processes. For each repetition 0 through 4, run MQ10,
Katsura-6 and Cyclic-5 at GF(32003) and GF(2147483647), stage-off then stage-on on even repetitions,
reversed on odd repetitions (60 processes). Each repetition then has two separate MQ10 work-on
processes, one at each prime (10 diagnostics), followed by Katsura-11/M31 staged basis-only
(five weak-result repetitions). MQ10/Katsura-6/Cyclic-5 use the fixed conversion/recovery route.
The Katsura-11 objective is a complete reduced grevlex basis. No direct-route or pilot completion
is silently inferred from these native cells; the two pilot tail cells remain unattempted.

Every child is limited to the smaller of 60 seconds and the remaining aggregate allowance,
2 GiB RSS, and 128 MiB output within the remaining 256-MiB cumulative scratch/archive allowance.
The hard aggregate cap is **900 seconds**, overriding the 4,500-second sum of child caps.
There are **zero automatic retries or native resumptions**. A compiler/load refusal preserves
its accepted prefix and stops. Work diagnostics remain separate from native timing distributions.
The measured pilot source/executable and independent answer identities stay frozen.

Only launch after the coordinator has established the next exclusive measurement window:

```sh
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=3 \
  tools/benchlock.sh m28-current-native-751 taskset -c 3 \
  timeout --signal=TERM --kill-after=5 900 \
  python3 tools/external/whole-route-study.py \
    --binary /buildcache/cargo-target/zeebra-751/release/examples/mq10_profile \
    --scratch /buildcache/cargo-target/zeebra-751/native \
    --output research/m28-current-baseline/native.json.gz \
    --phase native --build-commit "$BUILD_COMMIT"
```


The native launch retained exactly the first two planned cells (MQ10/GF(32003), stage-off/on)
and then refused before the M31 cell when an unrelated compiler appeared. `native.json.gz`
preserves this 2/75 prefix and the pre-child refusal. The accepted cells are not retried or pooled
with the four pilot observations. Five-repeat distributions, work diagnostics, all five native
Katsura-11 attempts and the two original pilot tail cells remain incomplete. Issue #751 is open;
its PR is draft. The [current report](../../docs/research/m28-current-baseline.md) states the blocker
and each acceptance item's incomplete status.


## Explicit one-time native amendment

A separately reviewed amendment permits only the **73 unexecuted cells** of the original native
grid. It is not an automatic resumption or a fresh campaign allowance. Preserve `native.json.gz`,
its two verified attempts and its compiler refusal unchanged. Its SHA-256 is
`3a733e31cf1d70ad27d322f2e950cd736676b4726ccb8004a8fa0754d6b1bd8f` and its original controller is
`9e2017806b95cbf88a904ad9213d324c2a1f5b0e`. The amended controller implementation pin is
`5e2bf3d8fa557845b18a60499b61a88f564e7e2c`; the actual launch HEAD is stamped separately in `resumptions.controller`.
Rust/example/Cargo source and the executable remain exactly the frozen `65734435` build.

The original native lock window records nine seconds. Conservatively charge **20 seconds** for
that window, metadata and timestamp/cleanup granularity, leaving **880 seconds** under the original
900-second aggregate allowance. The amendment's outer hard watchdog is 880 seconds, with child
wall capped by the remaining allowance, 60 seconds maximum, and 2 GiB RSS. Shared original native
scratch, the immutable original native archive **and** the amended archive count against the same
256-MiB cumulative output allowance. The old two responses are copied without alteration or rerun.

The explicit flag rejects altered identities/references, nonmatching or previously resumed prefixes,
failed/contaminated prefixes, and a second amended output. A new environmental gate or child
failure/refusal/contamination stops this last window and remains retained. No further amendment,
retry or limit increase is authorized. The two original pilot tail cells stay separate and are not
completed by native Katsura runs. The pilot and native cohorts are never pooled into repetitions.

After the coordinator confirms the quiet gate, launch only this committed amended plan:

```sh
ZEEBRA_MACHINE=trpro-5995wx ZEEBRA_AFFINITY=3 \
  tools/benchlock.sh m28-current-native-amendment-751 taskset -c 3 \
  timeout --signal=TERM --kill-after=5 880 \
  python3 tools/external/whole-route-study.py \
    --binary /buildcache/cargo-target/zeebra-751/release/examples/mq10_profile \
    --scratch /buildcache/cargo-target/zeebra-751/native \
    --output research/m28-current-baseline/native-completed.json.gz \
    --phase native --build-commit "$BUILD_COMMIT" \
    --native-amendment-from research/m28-current-baseline/native.json.gz
```

The amendment is allowed once; any blocked or incomplete result remains draft. If it completes,
offline validation checks all 75 cells while verifying the immutable original prefix, original
refusal, source/reference identities and cumulative budget ledger. This documents the explicit
exception to the original no-resumption plan without rewriting that plan or its first stop.
