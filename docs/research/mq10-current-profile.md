# Current-default MQ10 profile (#709)

**Measured at:** `5409f2bf`, 2026-11-12, after merging #705, #707 and #708
(`main` at `832a53d1`). Native cycle sampling uses `a7a11368`; only the campaign
runner and report changed, and the Rust executable has the same SHA-256. Production F4 code
is unchanged.

This experiment profiles the same public digest-pinned instances used by the grobx and sylvester
comparands, at GF(32003) and GF(2147483647), with the field representations used by `ZeebraSolver`.
`examples/mq10_profile.rs` changes only `F4Options::measure_stages`; the library and shipped
strategies are unchanged. Each process computes one reduced basis. Timers cover the F4 call,
not input generation/parsing or basis serialization. Process wall includes those boundaries.

Five alternating repetitions with and without stage clocks measure instrumentation overhead.
Every complete answer must match the full retained Singular-verified grobx basis, with the same
input digest and field; matching leading monomials alone is insufficient. All attempts and full
answers are retained. Construction sub-timers refine construction and never add to the stage sum.

A separate Callgrind run counts instructions in the clocks-disabled executable. Its simulated
wall clock and RSS are profiler costs and cannot become benchmark timings or engine memory figures.
Whole-process instruction counts include setup and serialization; source/function attribution is
used to locate code for investigation, not to equate instruction shares with elapsed-time shares.

## Native result: elimination owns the current cost

[Retained native cohort](../../research/competitive/results/mq10-profile-native.json.gz): all
20 attempts complete and match the full previously verified answers. Machine: Threadripper PRO
5995WX, affinity 0-3, one worker, under `benchlock`; no builds/tests overlap the measurements.
The lock records native START load 0.67 and END load 1.52. Compiler is Rust 1.99.1; the binary's
SHA-256 is `4d30e7d4861db796d2c98db6921dbd48ad98451119049fa5724f1cfb5c374ca6`.

Each cell below is a median of five fresh-process attempts. Stage percentages are medians of
within-run shares, so independently rounded medians need not sum to exactly 100%.

| F4 stage | GF(32003) | share | GF(2147483647) | share |
|---|---:|---:|---:|---:|
| symbolic preprocessing | 75.41 ms | 1.81% | 75.66 ms | 1.63% |
| matrix construction | 12.40 ms | 0.30% | 12.55 ms | 0.27% |
| elimination, including reduced-row back substitution | 4035.14 ms | 96.66% | 4502.54 ms | 97.01% |
| candidate extraction | 5.78 ms | 0.14% | 5.92 ms | 0.13% |
| final interreduction | 11.71 ms | 0.28% | 11.87 ms | 0.26% |
| outside these stages | 33.70 ms | 0.81% | 32.83 ms | 0.71% |

| control | GF(32003) | GF(2147483647) |
|---|---:|---:|
| F4 call, clocks disabled | 4164.58 ms | 4666.91 ms |
| F4 call, stage clocks enabled | 4174.49 ms | 4640.65 ms |
| clocks-disabled range | 4144.65–4169.75 ms | 4651.64–4804.23 ms |
| stage-clock range | 4152.82–4223.47 ms | 4632.47–4670.07 ms |
| control process wall | 4192.68 ms | 4695.83 ms |
| control process peak RSS | 134.43 MiB | 134.55 MiB |

The stage/control median ratios are 1.0024 and 0.9944. This sample resolves no systematic
instrumentation slowdown; a negative difference is timing variation, not an optimization.
These are profiling-executable measurements, with different boundaries and code layout from the
comparand harness. They do not establish a new cross-engine speedup or a regression against an
older cohort.

The old division-interreduction profile cannot prioritize this configuration. The final route
really is a matrix here, with no fallback: 252 rows, 606 columns, 247 output basis elements and
about 68,365 peak entries. Making final interreduction free would save only about 0.3%; making
*every stage except elimination* free gives only about 1.03x. A performance change intended to
address the new order-of-magnitude gap must reach elimination or change the amount of elimination
work. The stage is the one call to `eliminate_to` in
[`reduction.rs`](../../src/grobner/f4/reduction.rs); it includes the forward structured/adaptive
pass and the sparse reduced-row pass, not only the forward pivot-discovery kernel.

## Work and memory

The schedule and structural counts agree across all repetitions and clock settings. Both fields
run ten batches at degrees `2,3,4,5,6,6,6,7,7,8`, reduce 1,777 pairs, add 250 elements to the initial
ten, and return a 247-element reduced basis. Gebauer–Möller rejects 31,893 pairs. The independent
maximum row/column counts are 12,554/12,020; they are not claimed as a captured single matrix.

| counter | GF(32003) | GF(2147483647) |
|---|---:|---:|
| row operations, all batch elimination | 9,943,484 | 9,943,743 |
| back-substitution row visits/operations | 2,058,159 | 2,058,195 |
| peak live batch entries | 3,932,926 | 3,933,045 |
| entries as built in that peak batch | 783,727 | 783,737 |
| payload bytes per sparse entry | 16 | 16 |
| peak entry payload | 60.01 MiB | 60.01 MiB |
| largest adaptive dense buffer | 0.046 MiB | 0.092 MiB |
| peak basis terms | 71,183 | 71,184 |
| divisor queries | 52,249 | 52,249 |
| divisor scan steps | 1,253,051 | 1,253,051 |

`back_substituted_rows` counts visits to rows holding pivot columns, not distinct rows: each visit
performs one subtraction in
[`back_substitute_pivots_tracked`](../../src/linalg/sparse/elimination.rs). This accounts for
about 20.7% of the row-operation count, not necessarily 20.7% of elapsed time or instructions.
The remaining forward operations can have very different row lengths.

The measured entry payload alone is much larger than the earlier comparands' entire process
peaks. This makes an allocator-only explanation insufficient for the memory gap while retaining
this live-entry count and layout. A 32-bit coefficient still occupies a 16-byte `(usize, F)`
entry because of alignment. Even an eight-byte entry would leave about 30 MiB of payload at this
peak. Fewer live entries and a more compact representation are therefore concrete memory
investigations. These counters do not attribute the rest of RSS to a particular allocation site,
or establish the other engines' live-entry counts.

## Inside elimination: native samples confirm sparse row work

The [two complete Callgrind runs](../../research/competitive/results/mq10-profile-callgrind.json.gz)
use Valgrind 3.28.0, with cache and branch simulation disabled. Both pass the same full-basis check
and reproduce the native structural counters. Their complete instruction profiles are compressed
sidecars named in the cohort; reconstruct them with `gzip -dc` and use `callgrind_annotate`.
Grouping self events across source-file attribution gives:

| simulated instruction events | GF(32003) | GF(2147483647) |
|---|---:|---:|
| whole process, Ir | 94,107,979,750 | 98,847,585,283 |
| `SparseRow::subtract_scaled`, self including inlined code | 55.72% | 55.97% |
| libc copy implementation, self | 22.33% | 21.26% |
| dense `accumulator::eliminate_from`, self including inlined code | 18.89% | 19.85% |
| `back_substitute_pivots_tracked`, inclusive | 79.58% | 78.69% |

The inclusive row overlaps its callees and must not be added to self rows. Its 11 calls are ten
batch reductions plus final matrix interreduction. In GF(32003), the call graph attributes
2,058,440 sparse subtractions to this path, including final interreduction; the batch-only counter
above is 2,058,159. Thus the large sparse-subtraction share has a concrete caller, not just a
function name matching the suspected stage.

Callgrind emits a `brk segment overflow` warning, retained in each attempt's stderr, but both
processes complete and verify. Its simulated instruction proportions are not hardware cycle or
wall-time proportions, and its allocator/emulation environment differs. A separate native pass
is necessary before calling the copy routine the dominant native cost.

[Native cycle cohort](../../research/competitive/results/mq10-profile-perf.json.gz): five fresh
runs per field, all complete and full-basis checked. The exact same Rust executable runs under
`perf record -e cycles:u -F 997`, without stack capture. The tool is Fedora
`perf 7.3.3-200.fc44.x86_64`, executable SHA-256
`f4c9471ef6cb61cfbf1ec55d9580f64ea303a8f482cd4c75992dd32395f58d94`, downloaded and extracted
under `/buildcache` without changing system packages. Stack capture was unavailable under the
existing machine policy; flat user-cycle sampling works, and no policy setting was changed.
The cohort retains every complete text report and compressed `perf.data` sidecar.
Re-symbolizing raw samples requires the matching executable and DSOs; the retained text reports
remain usable without those local binaries.

| native self-cycle share, median of five | GF(32003) | GF(2147483647) |
|---|---:|---:|
| `SparseRow::subtract_scaled` | 53.32% | 57.35% |
| dense `accumulator::eliminate_from` | 25.56% | 24.18% |
| libc `memmove` | 8.53% | 7.07% |
| `back_substitute_pivots_tracked`, self | 6.94% | 6.53% |
| unresolved zero-address samples | 1.27% | 1.19% |

No report loses samples; each run contains about four thousand cycle samples. The sparse-row
share ranges 53.19–54.29% and 56.94–57.68%; dense accumulation ranges 25.33–25.69% and
24.17–24.36%. Unknown samples stay in the denominator. These are whole-process sampled-cycle
shares with no native call chains; the separate exact Callgrind call graph supplies caller
attribution. They do not constitute a native elapsed-time split between forward and backward
passes. Native source annotation places samples in the two-pointer merge, vector writes and
inlined field arithmetic in [`row.rs`](../../src/linalg/sparse/row.rs), rather than identifying
only the final copy-back call.

The native result corroborates the row-kernel bottleneck while materially reducing the copy
share from Callgrind's 21–22% to 7–9%. A pure copy optimization cannot recover the whole gap.
Neither dataset establishes a cache-miss rate, a DRAM bandwidth limit, or the cause of another
engine's advantage.

## What this prioritizes

The next focused experiment belongs in the F4 elimination work ([#269](https://github.com/mfaulk/zeebra/issues/269)): price the sparse
back-substitution work by target-row role and terms touched, then try reducing repeated full-row
merge work. Bulk handling of unaffected prefixes, a different accumulator for long rows, or
avoiding unnecessary reducer-row work are hypotheses to test, not measured improvements.
Any alternative must retain the full-basis checks and the row-capacity invariant from #554:
swapping the largest scratch buffer into every row previously inflated resident memory.

The representation work ([#268](https://github.com/mfaulk/zeebra/issues/268)) now has an explicit memory target: about 60 MiB of live entry
payload, in 16-byte entries at both field widths. Reducing the live matrix size is also relevant;
we have not measured how many rows or entries the other engines keep live. The next comparison
needs those counters before attributing the order-of-magnitude gap to a particular algorithm.

Final interreduction, symbolic divisor searches and column construction have small ceilings on
these cells. This report measures no optimization and changes no shipped default; its result is
which current work a proposed optimization must remove, and which performance claims remain
unmeasured.

## Reproduce

Build and test before acquiring the benchmark lock. Use a private target/scratch directory on
`/buildcache`; substitute a real machine name and an available CPU set. Commit the instrument
before running the campaign so retained provenance identifies the actual source.

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-mq10-profile
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
mkdir -p "$TMPDIR"
cargo test --example mq10_profile
python3 tools/test/mq10-profile-test.py
CARGO_PROFILE_RELEASE_DEBUG=1 cargo build --release --example mq10_profile

ZEEBRA_MACHINE=my-machine ZEEBRA_AFFINITY=0,1,2,3 \
  tools/benchlock.sh mq10-profile taskset -c 0-3 \
  python3 tools/external/mq10-profile.py \
  --binary "$CARGO_TARGET_DIR/release/examples/mq10_profile" \
  --scratch "$CARGO_TARGET_DIR/native" \
  --output "$CARGO_TARGET_DIR/mq10-profile-native.json.gz"

ZEEBRA_MACHINE=my-machine ZEEBRA_AFFINITY=0,1,2,3 \
  tools/benchlock.sh mq10-callgrind taskset -c 0-3 \
  python3 tools/external/mq10-profile.py --callgrind --repeats 1 \
  --binary "$CARGO_TARGET_DIR/release/examples/mq10_profile" \
  --scratch "$CARGO_TARGET_DIR/callgrind" \
  --output "$CARGO_TARGET_DIR/mq10-profile-callgrind.json.gz"
```

For optional native sampling, install your distribution's `perf` tool and pass its absolute
executable path. This records flat user-cycle samples and avoids build-ID cache writes:

```sh
DEBUGINFOD_URLS= ZEEBRA_MACHINE=my-machine ZEEBRA_AFFINITY=0,1,2,3 \
  tools/benchlock.sh mq10-perf taskset -c 0-3 \
  python3 tools/external/mq10-profile.py --perf "$(command -v perf)" \
  --binary "$CARGO_TARGET_DIR/release/examples/mq10_profile" \
  --scratch "$CARGO_TARGET_DIR/perf" \
  --output "$CARGO_TARGET_DIR/mq10-profile-perf.json.gz"
```

Keep outputs outside the checkout until the campaigns finish, then copy the cohorts and
profiler sidecars into `research/competitive/results/`; the runner refuses a dirty source tree.

The native guard allows 120 seconds and 2 GiB per process. Callgrind gets 1800 seconds and 4 GiB.
The guard sums the profiler and descendant process high waters conservatively, so a wrapper
cannot hide the measured child. A guard stop or nonzero exit is retained and fails the campaign. The binary hash, compiler, source
commit, options, field type, actual CPU affinity and complete statistics are recorded. The build
uses release fat LTO, one codegen unit and x86-64-v3, with line tables for instruction attribution.
No profiling row enters the competitive board, and no cross-engine ratio pools it with old runs.
