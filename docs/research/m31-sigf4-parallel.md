# M31-S2: parallel signature cascade, prereduce + claim (#904)

**Status:** complete, 2026-11-18. Gate B **passes** on Eco-12 / 2⁶⁴−353 at 16 workers; the code
merges as experimental behind `research-sigf4` (`SigF4Options::parallel_cascade`,
`sig_f4_study --claim`).
**Measured at:** `4b702ea3` (the #904 head, tag `measured/904-claim-cascade`) against `352fbd77`
(post-#903 `main`, design 1's reference), each built from a `git archive` of that commit into its own
target directory; binary SHA-256s in
[`research/m31-sigf4-parallel/binaries.sha256`](../../research/m31-sigf4-parallel/binaries.sha256).
**Plan:** [`MILESTONE-COMPETITIVE-SIGNATURE-F4.md`](../MILESTONE-COMPETITIVE-SIGNATURE-F4.md) §7.3,
§8.2, §8.5, §9, §10. **Design:** [`m31-parallel-signature-elimination.md`](m31-parallel-signature-elimination.md)
(#902) §3, §10, §12.

## 1. What was built

One design, the one #902 selected, in `src/grobner/sigf4/claim.rs` (engine hooks in `engine.rs`):

1. **Phase A** — every target reduced against the reducer block alone, on all workers (design 2's
   pass).
2. **Cascade pass** — targets taken in signature order. At an entry with no admissible reducer a
   target reads the column's write-once owner slot. An earlier owner's *final* row is applied as soon
   as the slot fills; an empty slot is trusted only once every earlier target has announced its lead
   or ended zero (a counter advanced over consecutive announcement flags). A target stores its slot
   and announces at its lead, and publishes its final row in a `OnceLock`.
3. **Accounting** — outcomes are handed to design 1's per-target accounting in signature order, so
   the syzygy, rewrite and pair stores are updated serially, exactly as design 1 does (#902 §9).

Every application is a row of design 1's pivot map `P_k`, and a target stops only with no entry in
`dom P_k`: Theorem 1's two conditions, so each row equals design 1's. Two refinements of #902 §12's
protocol keep that: the target polls the slot and the counter together (a filled slot is final
because it is write-once, and no later target can fill it first, since it announces only after
every earlier one); and the final-row slots are padded to their own cache lines.

| Requirement (plan §7.3, §9) | How it is met | Test (`cascade_tests.rs`) |
|---|---|---|
| Signature eligibility asserted on every pivot application | `check_signatures`: reducer and earlier-target pivots asserted below the target; a non-element pivot panics always (E2) | every test runs `SigF4Options::checked()` |
| Design 1's exact rows per batch | per-batch trace of every target's outcome and row | `test_claim_cascade_reproduces_design_1_rows_per_batch` (katsura-6 at two fields, cyclic-5, eco-7; both graded orders; 1–16 workers) |
| Zero reductions, singular rows, new elements | zero rows announce at their end; singular rows announce but are never pivots | `test_synthetic_batches_with_singular_rows_match_design_1` (the corpus has no singular rows) |
| Adverse schedules (E1) | seeded yields at every safe point, later targets let ahead, delayed announcement and publication | `test_adverse_schedules_keep_design_1_rows` (every worker count 1–16; asserts both wait kinds occur) |
| Bounded scratch and metadata charged to the live budget | sparse rows, phase-A and final rows, workspaces, slots and flags charged against `SigF4Options::max_live_bytes` (default: shipping F4's 320 MB) | `test_live_budget_is_charged_and_typed` |
| Wall-budget cancellation at batch and pivot safe points (E3) | deadline read at each target and every 1,024 pivot calls and wait rounds; a stopped batch is abandoned before any insertion | `test_wall_budget_abandons_the_batch_before_insertion`, `test_mid_batch_cancellation_inserts_only_complete_batches` |
| Correctness corpus (RFC §10.1, plan §10.3) | — | `test_correctness_corpus_matches_f4_at_16_workers` (GF(32003), Goldilocks; grevlex and grlex; certified); `test_small_systems_match_the_buchberger_reference` |
| No `unsafe` | none: `OnceLock`, atomics, `Mutex` | — |

The per-batch oracle is sharp: dropping the announcement wait fails the first test at two workers.

## 2. Method

Plan §10.4. Three suites in one session, n = 9 each, fresh process per child, arms rotated one place
per repetition (`research/m31-sigf4-parallel/campaign.py`, which reuses #901's child runner:
CCD-aligned `taskset` from CPU 8, `cpu-context` snapshots, frequency sampling, 180 s cap,
`rss-guard` at 8 GiB). CCDs 1–2 reserved with `tools/bench-reserve.sh` for the session and released
after it; everything ran under its benchlock. Machine 1-minute load 2.0–12.4 outside the reservation
(other sessions' builds, up to 33 compiler processes; the reservation fences their CPUs, not DRAM
bandwidth or package power). One `rss-guard` /proc read failed on one MQ11 design-1 child; peak RSS
there comes from the binary's own report, as everywhere.

Arms: **d1** design 1 (`--engine sigf4 --workers 1`, CPU 8) from `352fbd77`; **s2** this design
(`--claim --workers W`, CPUs 8..8+W−1), **d2** design 2 and **f4** shipping F4 (`--engine f4`), from
`4b702ea3` (plan §10.2: shipping F4 built from the evaluated tree). Ratios are paired per repetition;
intervals are 95% bootstraps of the median (20,000 draws). All 153 children completed; every row's
basis digest is identical across arms and repetitions.

## 3. Gate B (plan §8.2): **pass**

Eco-12 / 2⁶⁴−353, 16 workers (`research/m31-sigf4-parallel/tables.md`):

| Arm | n | Process wall ms | Elimination ms | Products | Peak RSS MiB |
|---|---:|---:|---:|---:|---:|
| d1:1 | 9 | 2,580.4 | 1,351.8 | 610,820,323 | 163.3 |
| d2:16 | 9 | 2,011.1 | 669.0 | 742,988,440 | 170.0 |
| s2:16 | 9 | 1,716.9 | 370.2 | 742,988,440 | 169.6 |
| f4:16 | 9 | 2,427.4 | — | — | 200.4 |

| Criterion | Value | Read |
|---|---|---|
| Elimination stage ≥ 2.5× faster than design 1 | **3.65×** [3.59, 3.76] | pass |
| Complete wall ÷ design 1: median ≤ 0.75, 95% upper ≤ 0.80 | **0.664** [0.655, 0.668] | pass |
| Products ≤ 1.25× design 1 | **1.216×** (phase A's redundant work, as #902 priced it) | pass |
| Peak RSS ≤ 1.25× design 1 | **1.039×** [1.034, 1.048] | pass |
| Every §9 check | §1's table; digests equal design 1 and shipping F4 on every child | pass |

Measured elimination at 3.65× sits between #902's greedy bound (4.63×, products only) and its
calibrated estimate (≈ 3.9×), and above Gate A's calibrated-greedy sensitivity row (2.82×).

## 4. Against shipping F4-16, and the other rows

Complete process wall, s2:16 ÷ f4:16, paired:

| Row | s2 ÷ F4-16 | s2 ÷ d1 | Elimination d1 ÷ s2 | Products s2 ÷ d1 |
|---|---:|---:|---:|---:|
| Eco-12 / 2⁶⁴−353 | **0.708** [0.706, 0.710] | 0.664 [0.655, 0.668] | 3.65× | 1.216 |
| Katsura-11 / Goldilocks | **0.446** [0.437, 0.456] | 0.636 [0.622, 0.663] | 6.02× | 1.000 |
| MQ11 / Goldilocks | **0.444** [0.437, 0.456] | 0.396 [0.389, 0.405] | 11.19× | 1.000 |
| Cyclic-7 / Goldilocks | 4.602 [4.476, 4.656] | 1.054 [1.014, 1.071] | 0.76× | 1.020 |

**#905's Target criterion 1** (plan §6.2: Eco-12 / 2⁶⁴−353, signature path ÷ shipping F4, median ≤
0.75 and 95% upper bound ≤ 0.80): **0.708 [0.706, 0.710], met** by this code as measured here. §6.2 is
scored on the final M31 code through the opt-in entry point, so this is the entry evidence for #905,
not its verdict. Cyclic-7 is the unfavourable control as expected: the parallel cascade does not
help it (small batches; the per-batch thread team costs more than the cascade saves), and
criterion 3's dispatch belongs to #905.

Worker curve, Eco-12 (s2 only):

| Workers | Process wall ms | Elimination ms |
|---:|---:|---:|
| 1 | 2,932.8 | 1,705.3 |
| 4 | 1,881.7 | 608.9 |
| 8 | 1,725.2 | 431.4 |
| 16 | 1,726.1 | 371.2 |

At one worker the design is design 2's products done serially, hence slower than design 1.

## 5. What shaped the implementation

Exploratory single runs on builds between `1fbd26ce` and `4b702ea3`, not gating: the first build's cascade pass was
*slower* at 16 workers (≈ 370 ms) than at 4 (≈ 276 ms), insensitive to spinning versus yielding,
and capping the cascade at 3–4 threads recovered it. Two changes removed the inversion and made the
pass scale (≈ 211 ms at 16): padding the per-target final-row slots to their own cache lines (16
spinners were polling slots that shared lines with slots being written), and waiting on the owner
slot or the counter, whichever comes first. Neither changes what is applied, so Theorem 1 still
covers it. What remains of Eco-12's 370 ms is roughly 45 ms of serial setup, 100 ms of phase A and
210 ms of cascade pass.

## 6. Caps (plan §8.5)

- One design. No displacement.
- About 590 net lines under `src/grobner/sigf4/` excluding tests (`claim.rs` less its test-only
  adversary, plus the engine and options changes), against 2,500.
- One session (one claim lease) to a correct end-to-end result and the gate read, against 8 and 12.
