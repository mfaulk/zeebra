# A pinned sdiehl/groebner F4 comparand (#678)

**Measured at:** `4a3c5b67` for the corrected cohort; initial diagnostic cohort at `5b3e6061`.
Both are on base `6e7bc27f`. The corrected source patch id is
`e7508c5d982a5f57214486193f21ca55c2e6a665`; every record also carries its own source/base/patch id.

The adapter admits a result only after the engine echoes the same ring and generators and its
**entire monic reduced basis** agrees with an independently computed Zeebra basis. The new
comparand is useful on these controls: it agrees in every measured run, and its F4 stage is faster
on random MQ6 while Zeebra is faster on the tiny wide-prime control. These are bounded public
algebra controls, not frontier or thread-scaling results.

## Source and build

The standalone [driver](../../tools/external/groebner-driver/README.md) calls
[`groebner_basis_f4(input, true)`](https://github.com/sdiehl/groebner/blob/c3e1d630fba9b2155a4c389d9022f13e0ba09218/src/f4/mod.rs)
at upstream `c3e1d630fba9b2155a4c389d9022f13e0ba09218` (0.6.0, MIT). It uses the engine’s
[runtime prime-field ring parser](https://github.com/sdiehl/groebner/blob/c3e1d630fba9b2155a4c389d9022f13e0ba09218/src/ring.rs),
then reads the ordered variables, modulus and order back from that ring and renders generators
from the parsed polynomials. No upstream implementation is copied into Zeebra. The root runtime
dependency graph and root `Cargo.lock` are unchanged.

Rust 1.99.1 (`58cf8f9c3`, LLVM 23.1.1), release, fat LTO, one codegen unit, `x86-64-v3`, system
allocator. The standalone manifest/lock/toolchain are committed; upstream default `parallel` is on,
`mimalloc`, `parameters` and `ffi` are off. Effective profile/flags, complete compiler identity and
source/lock hashes travel in the driver’s raw JSON. The corrected binary build identity is
`9c72be299136ca261791ce9d22a5b0744a17b15f38b4b9a964fad5ca8a8113e3`.
The prime-field implementation may use randomized row combinations even at one worker; no
unexposed random seed is claimed. Every retained answer is independently checked.

## Controls and operating conditions

Eight digest-pinned cells: Katsura-4, Cyclic-5 and random-MQ6 at 32003 and 2147483647, plus a
focused two-variable control at 18446744073709551263 and 18446744073709551557. The latter is
`x1^2 + 2*x1*x2 + x2^2 - 1, x2^2 - 4`, with the known root (-1, 2), dimension four and separately
pinned field digests. Its registration is separate from the public ladder. Only a two-variable
Zeebra instantiation was added for the second wide prime; no broader instantiation is implied.

Three repetitions, reversing engine order on alternate repetitions, one engine/digest per new
process. One- and four-worker cohorts are distinct. The actual Rayon pool size is echoed from
inside the pool and checked; configured workers are not a claim of full CPU utilization. Zeebra’s
configured F4 is serial, so all its four-worker attempts are explicit capability refusals.

AMD Threadripper PRO 5995WX, affinity 0–3 for both engines. Each solver gets 30 s and 1 GiB RSS;
the parent guard gets 95 s and 1 GiB RSS, polling every 2 ms and terminating its process group on a
crossing. Child RSS enforcement is sampled; completed child snapshots beyond the cap are also
refused. Two extra diagnostic attempts request a zero-byte cap and a zero wall limit and retain
the resulting memory and wall stops. They are not resource-threshold measurements.

The corrected benchmark-lock window ran on 2026-11-11, 21:26:05–21:26:11 −05:00, with load
0.33 at start and 0.47 at end, ending `status=0 end=exited`. No builds ran in the window. Each
one-row harness queries `rustc -Vv` for metadata before measuring its solver.

## Retained results and timing boundaries

The [corrected cohort](../../research/competitive/results/groebner-rs-678-v2.json) retains 98
attempts: 48 verified new-comparand answers, 24 Zeebra baseline answers, 24 Zeebra multiworker
refusals and two resource stops. Complete basis text, engine-parsed generator echoes, input
digests, actual workers, raw driver JSON, verification notes, startup observations and guard
observations are retained. All 48 new answers pass full coefficient/exponent agreement; zero
wrong answers or unavailable configurations were dropped.

`solve` is the upstream canonicalized F4 call, paired with Zeebra’s `basis` stage. Driver parsing,
pool creation, rendering and serialization are separate; harness output parsing and independent
verification are separate again. Verification runs after the child exits, so it contributes to
neither child solve time nor child wall/CPU/RSS. The quotient dimension is inferred from the
matching trusted basis; it is not presented as an independently reported driver invariant.

The following are **ratios of three-run medians of engine stages**, one worker versus one worker.
Above one means the new engine’s stage is faster. No wall-to-engine ratio is used.

| control | characteristic | Zeebra basis | groebner-rs solve | Zeebra / groebner-rs |
|---|---|---|---|---|
| `katsura-4` | 32003 | 162.638 µs | 217.101 µs | 0.75x |
| `cyclic-5` | 32003 | 905.003 µs | 714.192 µs | 1.27x |
| `mq-random-6` | 32003 | 12511.516 µs | 3197.834 µs | 3.91x |
| `katsura-4` | 2147483647 | 150.836 µs | 194.929 µs | 0.77x |
| `cyclic-5` | 2147483647 | 861.421 µs | 753.035 µs | 1.14x |
| `mq-random-6` | 2147483647 | 13500.810 µs | 3729.801 µs | 3.62x |
| `groebner-rs-wide-control` | 18446744073709551263 | 45.095 µs | 103.967 µs | 0.43x |
| `groebner-rs-wide-control` | 18446744073709551557 | 50.876 µs | 93.818 µs | 0.54x |

On MQ6 the new engine is 3.62–3.91x faster internally in this cohort. The 2147483647 Cyclic-5
ratio is inside the project’s 20% noise band; the small controls do not establish a general
ordering of engines. The wide-prime arithmetic controls exercise representation and agreement,
not the large-matrix regime. No four-worker speedup over Zeebra is reported because there is no
matched multiworker Zeebra operand. The board rejects worker, resource, build, machine, policy or
source-revision mismatches, and uses the declared stage-resolution gates for engine ratios.

The separately observed driver loader-only floor is 10.271–10.405 ms, including the supervisor’s
10 ms polling/reap cadence. Small whole-process rows are therefore startup/poll dominated, and
wall ratios must not be read as engine ratios. Child CPU is a `/proc` tick observation at 100 Hz,
so zero ticks on a short process means quantization, not free computation.

## Memory observations and the initial measurement defect

The initial [98-attempt diagnostic cohort](../../research/competitive/results/groebner-rs-678.json)
at `5b3e6061` also passed every complete basis check. Its child RSS readings were sometimes only
20–88 KiB: the process completed between supervisor polls and the last observation described
startup, not the computational peak. Those observations remain retained and the generated board
marks them as **last live polls**; they must not support a memory-efficiency conclusion.

Contract 2 reads the child’s own kernel `VmHWM` after basis rendering and a black-boxed trial JSON
encoding, supplements any supervisor observation and records `ChildSelfHighWater`. The corrected
48 answers report 2.87–3.95 MiB. Final stdout/exit allocations follow the snapshot; this is a
kernel observation of the completed computational phase, not `wait4` exit resource usage. The
in-process Zeebra figure includes its harness image, so no cross-engine memory-efficiency ratio
is claimed from these controls.

Regeneration exposed two further evidence-loss bugs: RSS provenance became `unavailable`, and
memory/wall stop text was reclassified as a tool-owned cap. Failing tests captured both. Stored
RSS descriptions and opaque recorded stop reasons now survive regeneration unchanged. The
initial attempts’ original metadata was restored from their authoritative cohort file before
appending the corrected attempts; no observation was edited. The preceding 714 published rows
are unchanged. Both 98-attempt cohorts are retained, giving **910 attempts** in the main history.

## Reproduction and validation

Follow the [external-engine guide](../guide/external-engines.md#pinned-rust-f4-comparand): provision
the locked driver, build the one-row runner, then run `tools/external/groebner-cohort.py` under
`tools/benchlock.sh` with actual affinity matching `ZEEBRA_AFFINITY`. The script retains all
outcomes and full artifacts. `--append-history` appends explicitly; `competitive --write` measures
nothing and regenerates the display. The source hashes and original basis artifacts permit an
audit without relying on the Markdown summary.

The core changes followed Red–Green tests: ring round trips, exact metadata and full-basis checks,
RSS enforcement, visible worker counts, and lossless history provenance/resource reasons.
Regular tests, live driver checks, the pinned standalone workspace tests, Clippy with/without root
default features and doctests validate the implementation. Driver CI tests its independent locked
workspace; root CI does not acquire the upstream dependency. External record struct literals and
exhaustive outcome/RSS matches must accommodate the documented API additions.
