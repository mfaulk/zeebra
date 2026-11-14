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
That is 75 attempts, a 1,800-second hard aggregate cap and the same child/output limits. The
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
