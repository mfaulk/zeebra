# Public univariate-eliminant comparisons (#456, #482)

**Measured at:** `cbcdf5a0`, base `ff757b7f`, patch id
`7c8391ccc17bd5e301607d35d12d8411cdb2aa53`, on 2026-11-10 (America/New_York).

The retained cohort adds **60 attempts** to the previous 550 rows: all five engines on eleven
public rungs at `GF(32003)`, plus one five-engine capability check on `katsura-4` at `GF(2147483647)`.
The original 550 records are preserved, in order and field for field. The artifact is
[`research/competitive/results/history.json`](../../research/competitive/results/history.json);
[`COMPETITIVE.md`](../../research/competitive/COMPETITIVE.md) is generated from it.

## Method and correctness

Machine `fedora`, AMD Ryzen Threadripper PRO 5995WX, pinned to logical CPU 2, one solver worker.
The build used rustc 1.99.1 (`58cf8f9c3`), `x86-64-v3`, fat LTO and one codegen unit. Both
`ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY` were set. Each process ran one rung and one task, with a
120-second solver wall limit. Each small-prime rung had an external 32 GiB RSS guard; all guards
returned success. The extra reference-prime check used the same small Katsura rung and wall limit.

`tools/benchlock.sh` serialized the runs. Its start/end one-minute load averages were 2.20/2.46,
1.22/1.03 and 1.03/1.44 for the three batches. The first binary completed and appended its five
records before the launcher's final `tail` hit a closed output pipe (exit 141); subsequent batches
redirected their complete output to files and exited normally. No incomplete computation is
presented as an answer.

Versions are recorded per attempt: Singular build 44105, msolve 0.11.0, Groebner.jl 0.10.11 on
Julia 1.11.7, and Sagebrush `86d9f1c787030752dcaab1ddb8d99cf1b7fa5e1b`, built for x86-64-v3.
Zeebra used its defaults (`interreduction=by-order`, `batch-rows=reduced`).

Before measurement, `test_real_small_prime_eliminants_agree_as_polynomials` compared Zeebra,
Singular and msolve on the published `katsura-4` ideal at `GF(32003)`, as parsed polynomials rather
than strings. The complete lex basis is not the task: every engine must return a generator of
`I ∩ k[x_n]`. In particular, Singular prints the relevant basis element **first**, not last;
the adapter now extracts that element and its degree.

Every answered pair in this cohort has the same reported eliminant degree, nonempty invariant
overlap and no shared-invariant disagreement. The board enforces those checks for both wall and
engine-internal ratios. Degree agreement is a necessary invariant, not a proof of polynomial
identity on every measured rung. The startup-floor and stage-resolution gates are unchanged.
Engine-internal eliminant times charge basis construction and conversion, not just F4.
The renderer now reads msolve's actual slash-separated stage labels (`f4/overall(elapsed)` and
`sparse-fglm/overall(elapsed)`); its earlier colon-separated selector matched none of these
retained rows. This correction changes derived comparisons, not the stored measurements.

## Results at GF(32003)

Each cell is one measurement, with no claim of sub-20% precision. Times include each engine's
chosen route to the eliminant: Singular computes a lex basis directly; Zeebra converts a grevlex
basis; msolve uses its parametrization route. Different algorithms are permitted for this common
output, and these are not isolated FGLM-stage timings.

| rung | eliminant degree | Zeebra | Singular | msolve |
|---|---:|---:|---:|---:|
| `katsura-4` | 8 | 0.189 ms | 37.709 ms | 11.611 ms |
| `katsura-5` | 16 | 0.583 ms | 37.230 ms | 11.597 ms |
| `katsura-6` | 32 | 1.834 ms | 47.917 ms | 11.593 ms |
| `katsura-7` | 64 | 8.822 ms | 238.226 ms | 11.586 ms |
| `katsura-8` | 128 | 49.996 ms | 4,074.071 ms | 11.591 ms |
| `katsura-9` | 256 | 379.432 ms | 118,968.547 ms | 41.870 ms |
| `katsura-10` | 512 | 3,010.902 ms | 120 s limit | 213.420 ms |
| `cyclic-4` | — | unsupported | unsupported | failed |
| `cyclic-5` | 15 | 1.260 ms | 37.232 ms | failed |
| `cyclic-6` | 48 | 7.471 ms | 104.331 ms | failed |
| `cyclic-7` | 203 | 552.387 ms | 17,300.962 ms | failed |

The cohort has **28 completed, 27 unsupported, four failed and one stopped-by-limit** attempts.
All outcomes are retained. A limit is not a completion time.

- `katsura-9`: Zeebra 379.432 ms versus msolve 41.870 ms, **9.06x behind**.
- `katsura-10`: Zeebra 3,010.902 ms versus msolve 213.420 ms, **14.11x behind**.

Both msolve comparisons clear the unchanged startup-floor gate. The smaller Katsura rows do not:
msolve's roughly constant startup time cannot license a speedup in either direction. Its internal
stage resolution also excludes some stage ratios that a wall measurement can distinguish.

These public results do **not reproduce the historical ~30x conversion-stage figure** on Anemoi at
`p = 65537`: they concern different ideals, a different field and a complete eliminant task.
The older figure remains a one-off, family-specific measurement outside the public corpus, as
[`competitive-baseline.md` §1](competitive-baseline.md#1-the-headline-zeebra-loses-to-msolve-on-order-conversion-and-the-reason-is-the-algorithm)
now states. No claim is made that #369's original acceptance item 2 is met for that removed row.

## Refusals and negative results

Groebner.jl and Sagebrush refuse this task on every rung. Sagebrush's lex-basis route is not
silently substituted for an eliminant. Neither offers the finite-field solution tasks either;
the per-adapter evidence and the second-objective decision are in the
[comparison protocol](external-comparison-protocol.md#eliminants-are-the-available-second-objective-456).

`cyclic-4` is positive-dimensional. Zeebra and Singular report that as unsupported; msolve's
existing parametrization parser classifies its corresponding output as failed. None supplies a
time for comparison. On `cyclic-5`, `cyclic-6` and `cyclic-7`, msolve adds a variable carrying a
linear form, so its output is about a different projection. The adapter's existing identity check
rejects those results, and the board publishes no msolve ratio for them. Changing genericity
handling to compare a different projection is outside this task.

The extra `GF(2147483647)` check confirms that an explicit eliminant request retains msolve's
characteristic refusal without suppressing Zeebra's and Singular's answers. The default sweep
omits the eliminant at that field; an explicit request still lets each adapter decide safely.

## Reproducing

Build the sweep at the measured commit (or reconstruct it from the base and patch id), source the
installed comparands, then repeat one row per process under the lock. The characteristic must be explicit:
legacy Zeebra `reproduce` strings name the rung and task but omit the field. The record's field
identity and the commands below resolve that omission.

```sh
. tools/external/env.sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-456
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=""
unset RUSTFLAGS
mkdir -p "$TMPDIR"
cargo build --release --example competitive_sweep
export ZEEBRA_MACHINE="$(hostname)" ZEEBRA_AFFINITY=2

# Repeat for katsura-4 through katsura-10 and cyclic-4 through cyclic-7.
tools/benchlock.sh eliminant taskset -c 2 \
  "$CARGO_TARGET_DIR/release/examples/competitive_sweep" \
  --row katsura-9 --task univariate-eliminant --characteristic 32003 \
  --wall 120 --measure --write

# The explicit high-prime capability check.
tools/benchlock.sh eliminant taskset -c 2 \
  "$CARGO_TARGET_DIR/release/examples/competitive_sweep" \
  --row katsura-4 --task univariate-eliminant --characteristic 2147483647 \
  --wall 120 --measure --write

# Back in the updated checkout holding the retained history and stage-label correction:
cargo run --profile ci-release --example competitive -- --write
```

Rendering takes no measurements, so its `ci-release` build does not alter any timing.

For the RSS guard, start `tools/rss-guard.sh competitive_swe` with the sweep binary's absolute
path, ceiling `33554432` KiB and an adequate `--wait` before each small-prime process, and wait for
its exit after that process finishes. Use a fresh guard per rung, not one guard around the loop.
The measured runs used a guard wait of 30 seconds inside the held benchmark lock.
