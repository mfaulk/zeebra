# F4 live budgets after reduced batch rows (#659, #490)

**Measured at:** `577a1678` for the original explicit-cap sweep, `ebb040da` for the new-default
sweep, and `3bf5c35b` for the supervised unbounded probe. Raw records retain the base and patch id
for each normal sweep row. The policy change preserves F4's algebra and the definition of a live
matrix entry.

## Decision

Raise `F4Options::recommended()` and `default()` to 32,000,000 live entries and 512,000,000 bytes.
Keep `baseline()` at 20,000,000 entries and 320,000,000 bytes. Explicit caller limits remain strict;
`with_live_entries` and `with_live_budget` still set both coupled limits.

The larger completed Anemoi regression target needs 24,011,204 live batch entries. A minimum 25%
margin requires more than 30 million entries; rounding to 32 million leaves 33.3% room. A 25-million cap
would leave only 4.1%. This is a bounded library policy for the measured reduced-row workloads,
not a claim that 32 million covers every system or that this workstation's RAM should be the
library default. Larger systems retain explicit caller-controlled budgets. Both live limits apply
to final matrix interreduction as well.
Over 40-byte BN254 entries the byte limit admits 12,800,000 entries, preserving a common byte
allowance across field widths. These limits do not cap process RSS.

## What the old table got wrong

The original entry count was arbitrary: `057b4b6f` introduced 20 million as a recoverability valve;
`b2283f1e` later derived the 320-MB byte budget from it. The history is retained in
[`f4-resource-scaling.md` §14](f4-resource-scaling.md#14-where-20-000-000-came-from-and-what-still-crosses-it-490).

An elimination refusal reports the entry count when a row operation crossed its allowance. That
count is not the run's eventual peak. Raising a cap just above the crossing therefore does not
establish that the run would complete. Construction now reports exact demand before allocating
rows (#557); that demand still does not establish the subsequent elimination peak.

The fresh explicit-cap sweep confirms the issue's reduced-row peaks, measured with a generous
64-million reference allowance:

| Input | At 20 million | At 64 million | Completed batch peak |
|---|---|---|---:|
| Anemoi, GF(65537), N=5 FCICO | entry refusal | complete, 109 basis elements | 22,530,520 |
| Anemoi, GF(65537), N=6 PCICO | entry refusal | complete | 24,011,204 |
| random MQ, 10 variables | complete | complete | 3,933,045 |
| Anemoi, GF(65537), N=4 FCICO | complete | complete | 928,555 |
| Anemoi, GF(65537), N=4 PCICO | complete | complete | 158,757 |
| Anemoi, GF(65537), N=5 PCICO | complete | complete | 2,026,887 |
| Poseidon, full 80-variable rf4/rp2 system | entry refusal | entry refusal at 64,001,732 | **unknown** |
| Cyclic-9, GF(2147483647) | entry refusal | entry refusal at 64,000,470 | **unknown** |

The full-width Poseidon input is unsliced. A refusal is inconclusive; it is not a statement about
whether that system has a solution. Likewise, restoring an Anemoi basis computation is not a
verified field point or a cryptanalytic frontier extension. Raising the default to 32 million is
not claimed to complete Poseidon or Cyclic-9. Their eventual peaks remain unknown, and no larger
default is justified from the crossing counts alone.

## Protocol and scope

One process per row, one worker pinned to CPU 2 on `fedora` (Threadripper PRO 5995WX), release,
x86-64-v3, fat LTO, one codegen unit, `--no-default-features`. Builds completed before measurements, which were serialized
under `tools/benchlock.sh`. Each process had a 16-GiB virtual-address ceiling, a cooperative
600-second F4 budget and a 630-second external watchdog. The original sweep's entire watchdog was
1,800 seconds. The limits are experiment ceilings, not a prediction of workload cost.

The instrument separates the completed-batch peak, final-interreduction reporting when present,
process RSS and the refusal message. A stopped run's `completed_peak_live_entries` excludes the
failed batch and must not be presented as its full-run peak. Single runs are sufficient to pin
these deterministic entry counters; no timing speedup is inferred from the single-run cohorts.
Completed reduced-basis digests are compared across caps before drawing a budget conclusion.

[`research/live-entry-budget/README.md`](../../research/live-entry-budget/README.md) documents the
instrument, pinned generator source, input export and reproduction. The large regression's small
polynomial fixture is kept under `src/grobner/f4/test-data/`; its expected 109-element basis digest
comes from the completed 64-million reference run. A release-only CI invocation runs that test
explicitly, including a second pass proving that an explicit 20-million limit still refuses.

## New-default re-sweep

All 28 ordinary sweep records are retained in
[`runs.json`](../../research/live-entry-budget/runs.json). Across caps, every completed system has
one exact reduced-basis digest. Completed reduced-row peaks also agree exactly. The eleven-variable
Katsura control was measured at explicit 20-million and 64-million allowances as well as the new
default; all three return the same 537-element basis and the same 9,772,252-entry peak. Its input
matches the competitive corpus's arity, guarded by the example's automated test.

The following are the new-default rows. MB is decimal; raw JSON retains bytes. Refused rows'
last-completed-batch counts are deliberately omitted from this full-run peak column.

| Input | Default outcome | Completed batch peak | Final matrix-interreduction peak | Process peak RSS |
|---|---|---:|---:|---:|
| Anemoi N=4 FCICO | complete | 928,555 | 10,675 | 29.7 MB |
| Anemoi N=4 PCICO | complete | 158,757 | 1,443 | 7.9 MB |
| Anemoi N=5 FCICO | complete | 22,530,520 | 91,497 | 510.7 MB |
| Anemoi N=5 PCICO | complete | 2,026,887 | 15,901 | 55.5 MB |
| Anemoi N=6 PCICO | complete | 24,011,204 | 353,740 | 586.7 MB |
| random MQ, ten variables | complete | 3,933,045 | 68,367 | 139.5 MB |
| Katsura, eleven variables | complete | 9,772,252 | 383,733 | 330.4 MB |
| Poseidon, full rf4/rp2 system | entry refusal at 32,001,042 | unknown | not reached | 1,381.1 MB |
| Cyclic-9 | entry refusal at 32,001,349 | unknown | not reached | 886.7 MB |

No completed new-default final interreduction fell back. The RSS rows show why the payload allowance must not
be advertised as a process-memory ceiling.

The current echelon-row control for N=5 FCICO completes at an explicit 20-million cap, with
1,543,889 peak batch entries and the same 109-element reduced basis. Its 88,166 maximum batch rows
become 27,570 with reduced rows; batch entries instead rise to 22,530,520, reproducing #659's
14.59x exchange. The echelon control's final matrix attempt fell back to division; its batch peak
is reported separately. Corresponding process peaks are 456.4 MB for echelon and 510.7 MB for
reduced rows. The policy retains reduced rows and admits their measured cost.

## Supervised unbounded Poseidon attempt

The same full-width input was then run with row, column, entry and byte limits lifted, while
retaining the 600-second cooperative wall budget and external supervision. The kernel's soft and
hard virtual-address limit was verified at 17,179,869,184 bytes (16 GiB). An external watchdog
allowed 660 seconds plus termination grace.

The process aborted on allocation after **174.03 seconds**, at **16,164,347,904 bytes** measured
peak RSS (15.054 GiB). The refused allocation was 316,224 bytes. GNU time collected the measured
child high-water mark; it is neither the supervising Python process's memory nor an entry-derived
estimate. The source, base, patch id, verified address limit and raw failure are retained in
[`poseidon-unbounded.json`](../../research/live-entry-budget/poseidon-unbounded.json).

This is a **bounded negative result**, with process exit status 134/SIGABRT and no returned F4
report or basis digest. GNU time's `%x` text says zero for this signalled child; it must not
supersede the actual nonzero exit status and `Command terminated by signal 6`. The supervisor
returned successfully after recording the failed child, not after a completed basis computation.
The allocation site is not attributed by this run, and the full successful live-entry peak remains
unknown. In particular, this is not evidence that a particular larger entry cap would finish.

The earlier typed F4 refusals independently establish demand beyond 64 million entries. Together
with this externally bounded attempt, they retire the claim that the original Poseidon stop was
a tiny budget miss. The default policy therefore restores the measured Anemoi regression envelope
rather than pricing an uncharacterized full-width campaign into every library call.

A Linux reproduction, after exporting the input and building the example, is:

```sh
(
  ulimit -v 16777216
  ZEEBRA_MACHINE=fedora ZEEBRA_AFFINITY=2 ZEEBRA_WALL_SECONDS=600 \
    tools/benchlock.sh live-budget-unbounded \
    timeout --signal=INT --kill-after=10s 660 taskset -c 2 /usr/bin/time -v \
    /buildcache/cargo-target/zeebra-659/release/examples/f4_live_budget \
    /buildcache/cargo-target/zeebra-659/poseidon31-cico-t16-rf4-rp2.system \
    unbounded reduced
)
```

A resource-stopped invocation returns nonzero; retain its stderr and external RSS evidence rather
than inventing an F4 completion record. The address-space ceiling is distinct from a resident-set
ceiling. Retain external time and memory ceilings when lifting internal limits.

## Reading historical records

Prior published figures retain their original policies. Reproduce a pre-change recommended
20-million-entry policy with `F4Options::recommended().with_live_entries::<F>(20_000_000)` plus
the record's strategy settings. `baseline()` also retains its old budget but deliberately selects
different strategies, so it is not a substitute for a historical recommended configuration.

The older Anemoi basis timings and pre-#575 echelon-row counts remain historical measurements;
they are not silently re-attributed to today's reduced-row strategy or larger default. The new
policy restores the reported completion without reverting #575's reduction strategy. Existing
competitive history is retained rather than repriced or overwritten; new measurements carry the
actual allowance in `environment.policy`. No comparison should pool different policies as one
configuration.
