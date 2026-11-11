# Sagebrush at the matched ISA floor (#520)

**Measured at:** `c033f027` (Zeebra); Sagebrush
`86d9f1c787030752dcaab1ddb8d99cf1b7fa5e1b` through driver contract 3.
Historical cohorts: `7adb29e` and `87a807e`, retained in the competitive history
with their `base_commit` and `patch_id` stamps.

The re-take covers the original 26 cells at each of GF(2147483647) and GF(32003):
Katsura 4–7, Cyclic 4–6, random MQ 6/10/14 and planted MQ 6/10/14, each for
`reduced-grobner-basis` and `lex-basis-by-conversion`. Both Zeebra and Sagebrush
are run at every cell, including unsupported cases and resource stops. The later
600-second Cyclic-4 conversion refusal is a duplicate capability check; it does
not require a second timed attempt. Cipher systems removed by #668 remain in the
historical archive documented in `research/competitive/CURATION.md` and are not
restored to the public algebra corpus.

This is a new comparison cohort, not a controlled experiment on the ISA flag.
Since the original cohorts, Zeebra's reduction routes changed, Sagebrush gained
parser/metadata fixes, and affinity changed from CPUs 0–7 to CPU 2. Historical
wall ratios below describe the movement of the board; they do not estimate the
isolated benefit of AVX2, LTO or any individual optimization. The old records
remain intact.

## Measurement conditions

The lock ran from 2026-11-11 15:35:11 to 15:43:47 EST, `end=exited`, status 0,
516 seconds. Its recorded one-minute load was 0.96 at START and 1.12 at END.
The retained ISA-only check used a second lock, `520-isa-confirm`, from
15:46:51 to 15:48:20 EST: 89 seconds, status 0, `end=exited`, load 2.18 → 1.56.

- Fedora host `fedora`, AMD Ryzen Threadripper PRO 5995WX, one worker, CPU 2.
- `rustc 1.99.1 (58cf8f9c3 2026-10-13)`, release, fat LTO, one codegen unit,
  `-C target-cpu=x86-64-v3` on both sides.
- Installed driver source and manifest compared byte-for-byte with this checkout;
  its Sagebrush checkout was verified at the pin above. Each retained Sagebrush
  version carries its own `built for x86-64-v3 or better (AVX2)` marker.
- Wall budget 60 seconds per engine, no declared process RSS cap; Zeebra retains
  its default F4/FGLM caps. Each cell runs in a new process so Zeebra's high-water
  RSS belongs to that cell. Sagebrush's supervisor observes child wall/CPU/RSS;
  its `solve` stage is kept separately from process wall.
- All cells run sequentially under `tools/benchlock.sh` with tag `520-sagebrush`.
  No builds or tests were launched by this session during the measurements.

## Retained results and historical movement

The re-take appended 104 records; the preceding 610 records are unchanged.
The two tasks below are abbreviated RGB (reduced grevlex basis) and conversion
(grevlex basis followed by FGLM to lex). Each wall quotient is Zeebra wall /
Sagebrush wall, computed **within its own cohort**. A larger quotient favors
Sagebrush. The before/after columns are descriptive; they are not cross-cohort
engine speedups. In particular, short subprocess walls near the roughly 10 ms
supervisor/startup floor cannot establish an engine comparison. The generated
board retains its startup and Sagebrush-maturity verdicts.

| prime | problem | task | old Sagebrush ms | matched Sagebrush ms | old wall quotient | new wall quotient |
|---:|---|---|---:|---:|---:|---:|
| 2147483647 | katsura-4 | RGB | 10.396 | 11.271 | 0.018x | 0.013x |
| 2147483647 | katsura-4 | conversion | 10.435 | 11.439 | 0.024x | 0.017x |
| 2147483647 | katsura-5 | RGB | 10.412 | 11.506 | 0.077x | 0.036x |
| 2147483647 | katsura-5 | conversion | 10.395 | 11.655 | 0.088x | 0.047x |
| 2147483647 | katsura-6 | RGB | 10.411 | 11.623 | 0.371x | 0.118x |
| 2147483647 | katsura-6 | conversion | 10.413 | 11.642 | 0.384x | 0.165x |
| 2147483647 | katsura-7 | RGB | 10.419 | 11.651 | 2.610x | 0.632x |
| 2147483647 | katsura-7 | conversion | 10.398 | 11.650 | 2.853x | 0.763x |
| 2147483647 | cyclic-4 | RGB | 10.404 | 11.261 | 0.015x | 0.009x |
| 2147483647 | cyclic-4 | conversion | failed | unsupported | — | — |
| 2147483647 | cyclic-5 | RGB | 10.402 | 10.913 | 0.170x | 0.080x |
| 2147483647 | cyclic-5 | conversion | 10.395 | 11.641 | 0.226x | 0.113x |
| 2147483647 | cyclic-6 | RGB | 10.375 | 11.639 | 1.277x | 0.480x |
| 2147483647 | cyclic-6 | conversion | 10.403 | 11.638 | 1.522x | 0.796x |
| 2147483647 | mq-random-6 | RGB | 10.431 | 11.642 | 2.474x | 1.086x |
| 2147483647 | mq-random-6 | conversion | 10.393 | 11.639 | 2.687x | 1.211x |
| 2147483647 | mq-random-10 | RGB | 334.882 | 314.350 | 86.632x | 14.248x |
| 2147483647 | mq-random-10 | conversion | 395.409 | 407.388 | 74.475x | 11.628x |
| 2147483647 | mq-random-14 | RGB | stopped-by-limit | stopped-by-limit | — | — |
| 2147483647 | mq-random-14 | conversion | stopped-by-limit | stopped-by-limit | — | — |
| 2147483647 | mq-planted-6 | RGB | 10.433 | 11.357 | 0.006x | 0.008x |
| 2147483647 | mq-planted-6 | conversion | 10.477 | 11.634 | 0.056x | 0.038x |
| 2147483647 | mq-planted-10 | RGB | 10.375 | 11.645 | 0.011x | 0.010x |
| 2147483647 | mq-planted-10 | conversion | 30.613 | 31.831 | 0.928x | 1.256x |
| 2147483647 | mq-planted-14 | RGB | 30.672 | 31.804 | 0.007x | 0.004x |
| 2147483647 | mq-planted-14 | conversion | 6349.366 | 6204.020 | — | — |
| 32003 | katsura-4 | RGB | 10.414 | 11.370 | 0.020x | 0.013x |
| 32003 | katsura-4 | conversion | 10.384 | 11.175 | 0.025x | 0.017x |
| 32003 | katsura-5 | RGB | 10.418 | 11.620 | 0.077x | 0.032x |
| 32003 | katsura-5 | conversion | 10.400 | 11.630 | 0.096x | 0.040x |
| 32003 | katsura-6 | RGB | 10.403 | 11.627 | 0.344x | 0.125x |
| 32003 | katsura-6 | conversion | 10.383 | 11.636 | 0.383x | 0.138x |
| 32003 | katsura-7 | RGB | 10.385 | 11.637 | 2.522x | 0.570x |
| 32003 | katsura-7 | conversion | 10.389 | 11.639 | 2.700x | 0.687x |
| 32003 | cyclic-4 | RGB | 10.375 | 11.101 | 0.015x | 0.010x |
| 32003 | cyclic-4 | conversion | unsupported | unsupported | — | — |
| 32003 | cyclic-5 | RGB | 10.396 | 11.645 | 0.160x | 0.072x |
| 32003 | cyclic-5 | conversion | 10.380 | 11.648 | 0.203x | 0.108x |
| 32003 | cyclic-6 | RGB | 10.434 | 11.641 | 1.248x | 0.450x |
| 32003 | cyclic-6 | conversion | 10.398 | 11.646 | 1.451x | 0.655x |
| 32003 | mq-random-6 | RGB | 10.377 | 11.657 | 2.836x | 1.148x |
| 32003 | mq-random-6 | conversion | 10.394 | 11.670 | 2.828x | 1.265x |
| 32003 | mq-random-10 | RGB | 323.492 | 324.574 | 88.683x | 12.595x |
| 32003 | mq-random-10 | conversion | 395.068 | 396.153 | 78.349x | 11.008x |
| 32003 | mq-random-14 | RGB | stopped-by-limit | stopped-by-limit | — | — |
| 32003 | mq-random-14 | conversion | stopped-by-limit | stopped-by-limit | — | — |
| 32003 | mq-planted-6 | RGB | 10.400 | 11.255 | 0.007x | 0.008x |
| 32003 | mq-planted-6 | conversion | 10.384 | 11.646 | 0.053x | 0.035x |
| 32003 | mq-planted-10 | RGB | 10.407 | 11.672 | 0.013x | 0.010x |
| 32003 | mq-planted-10 | conversion | 40.691 | 31.844 | 0.429x | 0.785x |
| 32003 | mq-planted-14 | RGB | 30.703 | 31.813 | 0.007x | 0.005x |
| 32003 | mq-planted-14 | conversion | 6537.753 | 6361.752 | — | — |

Across cells with both quotients, new/old quotient ranges from 0.140x to 1.830x. This includes startup-bound cells and changes to Zeebra; it is not an ISA-effect range.
The historical/new Sagebrush process-wall quotient ranges from 0.890x to 1.278x across completed pairs, also including startup-bound cells.

Sagebrush completes 46 cells, reaches the wall limit on four random-MQ-14
attempts, and refuses both positive-dimensional Cyclic-4 conversions. Zeebra
completes 44 cells: four random-MQ-14 attempts exceed its live-entry cap, both
planted-MQ-14 conversions exceed its 4096-dimension quotient cap, and it also
refuses the two Cyclic-4 conversions. Every pair of completed answers agrees on
all shared invariants. No failed harness/tool rows occurred.

## ISA-only results

| prime | problem / route | baseline median solve ms | matched median solve ms | baseline / matched |
|---:|---|---:|---:|---:|
| 2147483647 | mq-random-10 / f4 | 273.692 | 276.894 | 0.988x |
| 2147483647 | mq-planted-14 / fglm | 6310.149 | 5515.205 | 1.144x |
| 32003 | mq-random-10 / f4 | 280.991 | 281.583 | 0.998x |
| 32003 | mq-planted-14 / fglm | 6300.485 | 5504.257 | 1.145x |

All four ISA-only ratios, **0.988x–1.145x**, lie inside the project's 20% noise
band. The F4 medians are slightly slower at the raised floor and the FGLM
medians faster; three repetitions do not establish either as a win.
The matched build fixes comparison symmetry, but these trials supply **no
measurable ISA-only gain**. This is not a measurement of the historical LTO
change, nor a microbenchmark of scalar field multiplication.

The scalar-arithmetic assessment in `sagebrush-implementation.md` §8.3 remains
unchanged: these whole-driver results do not justify copying `nmod.rs`, and its
field-range restriction still applies. They also do not prove a property of
Zeebra's individual field operations. The runtime AVX2 elimination dispatch was
already available to the baseline build, consistent with the small measured
ISA-only differences.

## Reproduction

Provision the pinned tools with `tools/external/provision.sh`, then build the
measurement binaries before acquiring the lock:

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-520
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=
export CARGO_INCREMENTAL=1
mkdir -p "$TMPDIR"
cargo build --release --locked --example competitive_sweep --example competitive
. tools/external/env.sh
export ZEEBRA_MACHINE="$(hostname)" ZEEBRA_AFFINITY=2
```

Run the following loops inside one benchmark-lock invocation (for example save
them as a script and run `tools/benchlock.sh 520-sagebrush bash /path/to/script`):

```sh
for characteristic in 2147483647 32003; do
  for row in katsura-{4,5,6,7} cyclic-{4,5,6} mq-random-{6,10,14} mq-planted-{6,10,14}; do
    for task in reduced-grobner-basis lex-basis-by-conversion; do
      timeout --signal=INT --kill-after=10s 180 \
        taskset -c 2 "$CARGO_TARGET_DIR/release/examples/competitive_sweep" \
        --characteristic "$characteristic" --row "$row" --task "$task" \
        --engines zeebra,sagebrush --wall 60 --measure --write || exit
    done
  done
done
```

The outer timeout guards a stuck harness; an ordinary engine budget refusal is
retained by the adapters and the harness continues. The history is append-only,
so repeating the command appends another cohort's attempts. Regenerate the
Markdown without measuring with:

```sh
cargo run --release --example competitive -- --write
```

## Controlled ISA check

A separate driver-only check holds source, dependency lock, compiler, fat LTO,
one codegen unit and `CARGO_INCREMENTAL=1` fixed. Only `target-cpu` changes. It uses random-MQ-10 F4 and
planted-MQ-14 FGLM at both primes, three repetitions per arm, in the order
baseline/matched, matched/baseline, baseline/matched. Inputs, binary hashes,
normalized-output hashes and each process/solve duration are retained in
[`sagebrush-isa-520.json`](../../research/competitive/results/sagebrush-isa-520.json).
The matched driver was rebuilt with the retained lock before this controlled
check; its binary hash differs from the provisioned binary used on the board.
Both hashes are retained in the JSON, and the driver source/manifest and pinned
Sagebrush tree are unchanged. The exact dependency lock is
[`sagebrush-isa-520.Cargo.lock`](../../research/competitive/results/sagebrush-isa-520.Cargo.lock).

Both arms must return identical output after removing only `#seconds:` and
`#isa floor:`. That includes coefficients, generators, ring metadata, quotient
dimension and leading monomials. This establishes agreement between the builds;
it is not a new independent oracle for Sagebrush. The ordinary board and live
agreement checks supply the separate cross-engine evidence.

To rebuild the baseline arm after provisioning, use the retained lock in the
provisioned driver's directory and keep the target directory separate:

```sh
cp research/competitive/results/sagebrush-isa-520.Cargo.lock \
  "$ZEEBRA_EXT_PREFIX/sagebrush-driver/Cargo.lock"
(
  cd "$ZEEBRA_EXT_PREFIX/sagebrush-driver"
  RUSTC_WRAPPER= RUSTFLAGS='-C target-cpu=x86-64' \
    CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-520/sagebrush-baseline \
    cargo build --release --locked
)
```

This baseline keeps fat LTO and one codegen unit, so it isolates the ISA flag;
it does not reconstruct the original historical driver, which also lacked LTO.
Re-run the recorded inputs with the two binaries under the benchmark lock and
affinity, keeping the output away from the retained measurement file:

```sh
export ISA_BASELINE=/buildcache/cargo-target/zeebra-520/sagebrush-baseline/release/sagebrush-gb-driver
export ISA_MATCHED="$ZEEBRA_EXT_PREFIX/bin/sagebrush-gb-driver"
# Run the Python block below inside tools/benchlock.sh and taskset -c 2.
python3 - <<'PY'
import json, os, pathlib, subprocess, tempfile, time
record = json.load(open('research/competitive/results/sagebrush-isa-520.json'))
with tempfile.TemporaryDirectory() as scratch:
    for cell in record['cells']:
        path = pathlib.Path(scratch) / 'input.ms'
        path.write_text(cell['input'])
        expected = None
        for repeat in range(3):
            arms = ['ISA_BASELINE', 'ISA_MATCHED']
            if repeat % 2:
                arms.reverse()
            for arm in arms:
                start = time.perf_counter_ns()
                output = subprocess.check_output(
                    [os.environ[arm], str(path), '--order', cell['order'],
                     '--route', cell['route']], text=True, timeout=60,
                    env=dict(os.environ, SAGEBRUSH_THREADS='1'))
                wall = time.perf_counter_ns() - start
                lines = output.splitlines()
                normalized = '\n'.join(line for line in lines
                    if not line.startswith(('#seconds:', '#isa floor:')))
                if expected is None:
                    expected = normalized
                assert normalized == expected
                solve = next(line for line in lines if line.startswith('#seconds:'))
                print(cell['characteristic'], cell['problem'], repeat, arm, wall, solve)
PY
```

## Validation and scope

The coverage check was run before the re-take and failed with zero new records;
afterwards it checks 104 appended records, exactly one Zeebra/Sagebrush pair per
historical digest/task, equal limits and environment within each pair, the ISA
marker on every Sagebrush record, and agreement on every shared invariant when
both sides answer. No historical row is edited. The board renderer is run again
and checked for an identical result.

The sweep checks shared invariants, not every output coefficient. The separate
ISA experiment compares complete normalized outputs between builds. Existing
live Sagebrush tests check coefficients against Zeebra on smoke and lex-route
fixtures. None of these removes the existing Sagebrush maturity restriction or
makes its timings an authoritative state-of-the-art baseline.

This task changes measurement records and documentation, with no library,
adapter, CLI or source-comment changes. There is no new solver behavior for a
unit test or Red-Green implementation cycle. Existing committed-record and live
agreement tests validate the artifacts and installed adapter; the initially
failing coverage check validates the measurement requirement. Existing CI
already loads committed records and checks measurement provenance, so its
workflow needs no change.

Checks run (using the separate `/buildcache` target and scratch directories
above):

```sh
cargo test --profile ci-release --locked --test committed_records --test external_comparands
ZEEBRA_SAGEBRUSH_DRIVER="$ZEEBRA_EXT_PREFIX/bin/sagebrush-gb-driver" \
  cargo test --profile ci-release --locked --test external_comparands sagebrush \
  -- --ignored --test-threads=1
cargo fmt --all --check
bash tools/check-measurement-provenance.sh
git diff --check
```

The first command passes four offline tests; the second explicitly runs and
passes three live Sagebrush tests that the first command ignores. Julia-only
and broader cross-engine campaign tests were not run for this re-take.
