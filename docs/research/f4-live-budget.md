# F4 live budgets after reduced batch rows (#659, #490)

**Measured at:** `577a1678` for the original explicit-cap sweep; post-change measurements are
identified separately in the retained records. This study changes the default budget policy, not
F4's algebra or its definition of a live matrix entry.

## Decision

Raise `F4Options::recommended()` and `default()` to 32,000,000 live entries and 512,000,000 bytes.
Keep `baseline()` at 20,000,000 entries and 320,000,000 bytes. Explicit caller limits remain strict;
`with_live_entries` and `with_live_budget` still set both coupled limits.

The largest completed affected workload needs 24,011,204 live batch entries. A minimum 25% margin
requires more than 30 million entries; rounding to 32 million leaves 33.3% room. A 25-million cap
would leave only 4.1%. This is a bounded library policy for the measured reduced-row workloads,
not a claim that 32 million covers every system or that this workstation's RAM should be the
library default. Both live limits continue to apply, including to final matrix interreduction.
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
x86-64-v3, fat LTO, one codegen unit. Builds completed before measurements, which were serialized
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
