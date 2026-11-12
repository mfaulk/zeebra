# The pinned sylvester F4 comparand (#684)

**Measured at:** `3f8cff57`, 2026-11-12. Source is sylvester 0.4.0 at
`ea34ddf3c9b9a275265576cd881c39c0c473e9f9` (MIT OR Apache-2.0), linked only in the isolated
[driver workspace](../../tools/external/sylvester-driver/README.md). No runtime dependency is
added to the root library. Later packaging/extended-cohort changes are identified separately.

## Protocol and correctness

The driver pins Cargo.lock, Rust 1.99.1, release/fat LTO/one codegen unit, `x86-64-v3` and the
system allocator. Build identity is `cb806500fe959c3b58d438275e734817707484a02456226944eacbc952b84102`;
source/lock/compiler/settings hashes are retained with every attempt. F4 is explicitly selected.
Fields at or above 2^31, extension fields, other orders and other task types are unsupported.

Parsed ring variables, modulus and original ordered generators are echoed from upstream values.
Every admitted full monic reduced basis matches Singular build 44105 coefficient for coefficient,
with its version retained. The live controls also independently check both repaired historical
counterexamples from upstream `KNOWN_ISSUES.md`, plus zero, unit, nonradical and positive-dimensional
ideals. They do not claim that the pinned revision still has those old defects.

Raw F4 records the actual worker pool. Certified computation records a trace and is serial.
The certificate is verified by the independent v2 verifier; its accepted field, coordinate count,
ordered input coefficient/exponent arrays (including zeroes/duplicates) and basis must match the
request. Changed input/modulus and tampered bytes are rejected in tests. Exhaustion is distinct
from a rejected proof. No engine assertion of correctness replaces verification.

## Initial bounded measurements

[83-attempt cohort](../../research/competitive/results/sylvester-684.json.gz), three alternating
repetitions, public Katsura-4/Cyclic-5/MQ6/MQ10 at 32003 and 2147483647. Machine: Threadripper PRO
5995WX, `ZEEBRA_MACHINE=trpro-5995wx`, `ZEEBRA_AFFINITY=0-3`, under `benchlock`, builds/tests
finished first. Each engine/digest gets a fresh process, a 60 s child wall limit and 2 GiB RSS cap;
the complete harness group has a 185 s/2 GiB watchdog. Workers are one except for the separately
identified four-worker pilot/refusals. No results are pooled with the grobx cohort or older runs.

| outcome | count |
|---|---:|
| current-default Zeebra complete | 24 |
| raw sylvester verified | 27, including three four-worker pilot attempts |
| exact-certified sylvester verified | 18 |
| certified MQ10 deadline stops | 6 |
| deliberate raw wall/RSS stops | 2 |
| unsupported configurations | 6 |

Unsupported includes certified workers=4, the unmatched Zeebra four-worker requests and the wide
prime control. These are capability rows, never timing losses. All completed new-engine answers
are independently checked. The initial history remains unchanged; new rows are appended.

The substantial raw task clears startup floors. These are medians of three complete attempts,
with equal digest, task, field/order, worker count, resource policy and environment:

| MQ10 characteristic | current Zeebra wall | raw sylvester child wall | Zeebra / sylvester | Zeebra peak RSS | sylvester peak RSS |
|---|---:|---:|---:|---:|---:|
| 32003 | 4 322.740 ms | 394.264 ms | 10.96x | 136.73 MiB | 12.75 MiB |
| 2147483647 | 4 379.734 ms | 394.792 ms | 11.09x | 138.24 MiB | 12.64 MiB |

Child wall includes startup, parsing, calculation and output. Independent Singular verification
runs afterwards and is separately timed; it is not hidden inside raw solve time. RSS is the
median of per-process kernel high-water marks, with a child snapshot after serialization
preparation supplementing supervisor samples. CPU ticks can quantize small cells. The four-worker
pilot has no matched four-worker Zeebra operand and establishes no cross-worker speedup. A pool
size also does not prove every F4 stage used all its threads.

## Certification is a different objective

`sylvester-certified` includes trace recording, certificate writing, independent checking and a
second replay binding serialized evidence to the requested input/basis. The public API integrates
the first three costs, so the driver reports that combined cost explicitly. It does not invent a
writer-only timer. The additional binding replay is separately reported; this deliberately checks
the proof twice and is not a measurement of minimum possible certification cost.

Certified resource keys contain `objective=exact-certified-basis`; the board cannot compare them
with raw Zeebra computation or its different certification trust boundary. Only raw `solve`
enters the engine-internal ratio selector. All six initial certified MQ10 attempts reached the
60 s deadline; they supply bounds, not completed timings. Smaller certified controls completed.
The integrated API and watchdog do not identify precisely which proof phase owned a killed run.

Full v2 certificate bytes and their size are retained as lossless compressed proof sidecars.
`python3 tools/external/proof_artifacts.py COHORT.json.gz INDEX` checks their SHA-256 and
reconstructs the original child JSON. No certificate or failed attempt is silently discarded.
The [adapter guide](../guide/external-engines.md#sylvester) gives pinned provisioning and complete
cohort commands. Build before locking; do not infer a task speedup from a kernel or startup cell.
