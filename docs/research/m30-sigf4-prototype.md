# M30-S3: bounded signature-F4 prototype — results (#857)

**Status:** complete, 2026-11-17. Both designs the RFC allows were built, and both are correct on
every corpus output. The predeclared #858 entry threshold on the primary instance is **not met**.
**Measured at:** `2d589a80` (design 1, `sig_f4_study`) and `7d85eee5` (design 2,
`sig_f4_study_d2`); the shipping-F4 arm is the same binaries' `f4` engine, whose production source is
byte-identical to the M30 freeze `4f5784c5` (`git diff 4f5784c5 -- src/` touches only
`src/grobner/sigf4/`, `src/grobner/mod.rs` and a test-generator overflow fix in
`src/grobner/differential/field.rs`). `research/m30-baseline/` (#855) was not on `main`, so the
freeze commit is the baseline. Binary SHA-256s are in
[`research/m30-sigf4/binaries.sha256`](../../research/m30-sigf4/binaries.sha256).
**Plan / RFC:** [`MILESTONE-SIGNATURE-SYMBOLIC-F4.md`](../MILESTONE-SIGNATURE-SYMBOLIC-F4.md) §6.3;
[`signature-f4-rfc.md`](signature-f4-rfc.md) §9, §10.1, §12.

## 1. What was built

`src/grobner/sigf4/` behind the `research-sigf4` feature, with its own entry points
(`sig_f4`, `sig_f4_reported`), options, error and statistics types. Nothing on the shipping F4
path was changed, and no file #861 may own (`symbolic.rs`, `macaulay.rs`, `pairs.rs`,
`src/linalg/`) was touched. 1,317 lines under `src/` excluding tests (cap: 3,500).

- **Design 1 (RFC §9):** batched F4-RB under Schreyer shifted signatures; one pending entry per
  signature, batches by least signature degree; syzygy criterion over minimal Koszul and zero-row
  signatures; rewrite criterion by sig-lead ratio; explicit product criterion; symbolic
  preprocessing choosing for each column the least-signature reducer multiple; serial regular
  elimination (targets in increasing signature order, pivots of strictly smaller signature, results
  of the batch usable unmultiplied, after Lairez Algorithm 8); singular rows discarded; then the
  shipping minimal-basis and matrix interreduction. No handover, no randomization.
- **Design 2 (RFC §6.1 item 1):** design 1 with every target first reduced against the batch's
  reducer block in parallel, each pivot use checked against the target's signature, then finished
  serially in signature order against earlier targets' results. The serial finish replaces §6.1
  item 2's displacement claim, which keeps the engine deterministic; it is also why design 2 gains
  little (§3).

**One correction to the RFC's wording.** RFC §3.4/§9 say the rewrite order takes the *least*
sig-lead ratio. Implemented that way the engine lost pairs on katsura-4 (red test, commit
`2d589a80`). The canonical rewriter must be the **greatest** ratio, i.e. the multiple at `T` with the
smallest lead (EF Def 7.13's `⊴_rat`-maximal element). An element reduced from a multiple of `α`
has a larger ratio than `α`, and it must supersede `α`. Reducer choice is the least ratio, which
is the least signature at a column, and that is what the RFC's §9 item 4 describes.

## 2. Correctness evidence

- Unit and property tests (`cargo test --features research-sigf4 --lib grobner::sigf4`, 17 tests,
  in CI): exact equality with `f4()` on katsura-4 (GF(32003), Goldilocks; grevlex and grlex),
  cyclic-4, Eco-5, all four RFC §10.1 constructions at both fields, and 192 random small systems
  (GF(13) both graded orders, GF(32003) grevlex). Small systems also equal
  `buchberger_reference`. Every equality test runs with `certify_f4_output` (reduced, Buchberger
  criterion, generators in the basis) and with the exhaustive signature checks on. The checks
  assert `s(pivot) < s(target)` on every cross-target use, `lm ≤` the shifted signature monomial,
  and that no element top-reduces a new one at a smaller or equal signature.
- The §10.1 construction digests were pinned in the first #857 commit (`e9c2d0be`), before any
  timing: `src/grobner/sigf4/corpus.rs`.
- Typed refusals: lex → `Unsupported`; basis, wall, row and column budgets → the shipping
  `F4Error` variants inside `SigF4Error::Budget`.
- **Every measured run** (215 timed children across both designs, plus the 3 census runs) returned a basis whose SHA-256 equals
  the shipping F4's on the same row: the `bases identical` column of
  [`research/m30-sigf4/tables.md`](../../research/m30-sigf4/tables.md). Equal sorted text is
  coefficient-for-coefficient equality of the reduced bases.

## 3. Results

Protocol: fresh process per run, arms rotated per repetition, `timeout --signal=INT
--kill-after=60s`, under `tools/benchlock.sh zb-857` with no build running. Children were pinned
CCD-aligned from CPU 24 (CCDs 1–2 were reserved by another session). n = 9 on the gating rows and
n = 5 on the rest. Medians with 95% bootstrap intervals of the median ratio. Process wall.

### 3.1 Plan §2.2 quantities (identical across repetitions; design 1)

| Instance | pairs created | product | Koszul | zero-row | rewrite | duplicate | targets | reductions to zero | products (G) | on zero rows (G) | sig basis / reduced |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| `eco-12` / 2⁶⁴−353 | 1,775,561 | 353,641 | 597,883 | 689,359 | 27,951 | 103,841 | 2,898 | 1,013 | 0.611 | 0.336 | 1,885 / 743 |
| `katsura-11` / Goldilocks | 156,250 | 26,177 | 88,498 | 32,474 | 4,577 | 3,829 | 706 | 145 | 0.200 | 0.083 | 561 / 537 |
| `mq-random-11` / Goldilocks | 293,761 | 46,183 | 129,273 | 108,247 | 3,293 | 5,469 | 1,307 | 540 | 1.745 | 0.899 | 767 / 767 |
| `cyclic-7` / Goldilocks | 4,749,349 | 55,131 | 3,170,652 | 1,310,794 | 79,898 | 129,670 | 3,211 | 128 | 0.019 | 0.001 | 3,083 / 209 |

No row ended singular on any instance. Zero rows equal reductions to zero, since only targets are
reduced. "Pair rows adding no rank" is therefore the reductions-to-zero column. Coprime-lead
syzygies are counted under *product*, because the product check runs first and a coprime pair's
signature is its Koszul signature.

Against the shipping F4's serial census at the same commit (`census.jsonl.gz`, #835's instrument):

| Instance | F4 products (G) | F4 on zero rows (G) | F4 zero rows | sigf4 products (G) | work ratio |
|---|---:|---:|---:|---:|---:|
| `eco-12` | 5.924 | 5.512 | 6,331 | 0.611 | **9.7×** less |
| `katsura-11` | 4.556 | 4.241 | 3,936 | 0.200 | **22.8×** less |
| `mq-random-11` | 20.377 | 18.922 | 6,293 | 1.745 | **11.7×** less |

The criteria are sound and the work they avoid is real: Eco-12 needs 9.7× fewer products, against
grobx's 6.33× in #716's exact pairing. **The work saving does not become a wall saving on Eco-12.**

### 3.2 Bookkeeping, separately (design 1, one run, seconds)

| Instance | bookkeeping (queue, criteria, pairs) | symbolic | elimination | interreduction | sig metadata |
|---|---:|---:|---:|---:|---:|
| `eco-12` | 0.534 | 0.465 | 1.698 | 0.696 | 16.1 MiB |
| `katsura-11` | 0.019 | 0.162 | 0.587 | 0.108 | 1.1 MiB |
| `mq-random-11` | 0.032 | 0.453 | 4.084 | 0.553 | 1.4 MiB |
| `cyclic-7` | 0.517 | 0.122 | 0.145 | 0.019 | 10.8 MiB |

### 3.3 Process wall (medians; full table in `research/m30-sigf4/tables.md`)

| Instance | F4 1 worker | F4 16 workers | design 1 (serial) | design 2 (16) | d1 ÷ F4-16 [95%] | d2 ÷ F4-16 [95%] |
|---|---:|---:|---:|---:|---:|---:|
| `eco-12` (primary) | 12.722 s | 3.170 s | 3.638 s | 3.230 s | 1.148 [1.142, 1.154] | **1.010 [1.003, 1.018]** |
| `katsura-11` (second family) | 10.048 s | 1.742 s | 1.078 s | 0.843 s | 0.619 [0.615, 0.623] | **0.486 [0.481, 0.494]** |
| `mq-random-11` (reported) | 42.881 s | 6.029 s | 5.795 s | 3.085 s | 0.961 [0.957, 0.964] | 0.512 [0.509, 0.515] |
| `noon-7` (control) | 0.181 s | 0.205 s | 0.104 s | 0.124 s | 0.506 [0.488, 0.529] | 0.604 [0.592, 0.612] |
| `katsura-4` Goldilocks (control) | 0.005 s | 0.006 s | 0.005 s | 0.007 s | 0.936 [0.853, 1.012] | 1.092 [1.048, 1.196] |
| `katsura-4` 2⁶⁴−353 (control) | 0.005 s | 0.006 s | 0.005 s | 0.007 s | 0.928 [0.843, 0.990] | 1.102 [0.992, 1.213] |
| `cyclic-7` (non-regular control) | 0.280 s | 0.151 s | 0.855 s | 1.050 s | 5.647 [5.556, 5.742] | 6.965 [6.852, 7.046] |

Design 1 against the serial shipping F4: Eco-12 0.286 [0.285, 0.288], katsura-11 0.107, MQ11 0.135.
Peak RSS on Eco-12 is 1.05× (design 1) and 1.11× (design 2) the shipping 16-worker figure.

## 4. Gate S3 → S4 (RFC §10.2, applied as predeclared)

| #858 entry threshold | Evidence | Met? |
|---|---|---|
| ≥25% better process wall at 16 workers on the primary (`eco-12`), n ≥ 9, 95% interval ≤ 0.80 | best design: 1.010 [1.003, 1.018] | **no** |
| second family (`katsura-11`) ≥10% better, interval excluding 1 | 0.486 [0.481, 0.494] | yes |
| small controls: 95% upper bound ≤ 1.05 at 1 and 16 workers | `noon-7` yes; `katsura-4` no (upper bounds 1.098 and 1.066 for design 1 against 1 worker, 1.196 and 1.213 for design 2 at 16; a 5–7 ms process dominated by start-up); `cyclic-7` 5.6–7.0× slower | **no** |
| peak RSS ≤ 1.25× shipping | 1.11× on Eco-12; 3.5× on cyclic-7 | not on every row |
| correct, coefficient for coefficient, typed `Unsupported` for non-graded orders | yes | yes |

**Verdict: #858 stays blocked.** The primary threshold fails with both designs, and the RFC's
two-design limit is reached. By plan §13's stop rule the line ends here with a documented result:
the designs did not fail (both are correct), but neither clears the gate. The predeclared corpus and
thresholds were not changed after measurement.

## 5. Why the work saving does not become a wall saving on Eco-12

- **Serial stages the signature engine adds or keeps.** On Eco-12 bookkeeping (0.53 s), symbolic
  preprocessing (0.47 s) and interreduction of a 1,885-element signature basis (0.70 s) are serial.
  Together they are 1.7 s, more than half of the shipping F4's 3.17 s at 16 workers. The signature
  basis is 2.5× the reduced basis (RS §B.4's outgrowth, open question 2), and 1.78 M pair decisions
  are 6× MQ11's.
- **Design 2 parallelizes the wrong half of elimination.** Pre-reducing against the reducer block
  cut elimination from 1.70 to 1.22 s and raised products from 0.611 to 0.743 G. Most of Eco-12's
  elimination is the cross-target cascade within a batch, which design 2 leaves serial. §6.1 item
  2's least-signature displacement claim targets exactly that cascade, but it is a third design.
- **Where it does pay.** On `katsura-11` and `mq-random-11` bookkeeping is small and elimination
  dominates, so a 12–23× work cut gives roughly 2× over the 16-worker shipping F4. MQ11 is reported,
  not gating (RFC §12.1).
- **Non-regular control.** `cyclic-7` builds a 3,083-element signature basis for a 209-element
  reduced basis and is 5.6–7× slower: the outgrowth RS §B.4 and grobx's handover tests exist for.

## 6. Open questions answered (RFC §13)

1. Displacement scaling: not measured. Design 2 measured the reducer-block half only (§5).
2. Signature basis against reduced basis: Eco-12 1,885 / 743; MQ11 767 / 767; katsura-11 561 / 537;
   cyclic-7 3,083 / 209.
3. The product criterion catches 353,641 Eco-12 pairs before the signature criteria see them. Those
   pairs are also Koszul-covered (§3.1 note), so the count is attribution, not extra soundness.
4. Not checked (no Hilbert-series run).
5. Workstream P's interning would shorten symbolic preprocessing (0.47 s on Eco-12); it is not
   enough alone to reach 0.80.

## 7. Reproduce

```sh
T=/buildcache/cargo-target/zeebra-857
export RUSTC_WRAPPER="" CARGO_TARGET_DIR=$T TMPDIR=$T/tmp
cargo build -j24 --release --features research-sigf4 --example sig_f4_study   # at 2d589a80 / 7d85eee5
cargo build -j24 --release --features research-sigf4,research-work --example sig_f4_study   # census
for s in gate controls census; do   # design 1; gate2, controls2 with BIN=<design-2 binary>
  BIN=$T/bin/sig_f4_study WORK_BIN=$T/bin/sig_f4_study_work OUT=$T/m30 \
    tools/benchlock.sh zb-857 timeout --signal=INT --kill-after=60s 3600 \
    bash research/m30-sigf4/campaign.sh $s
done
python3 research/m30-sigf4/summarize.py research/m30-sigf4/{gate,controls,gate2,controls2}.jsonl.gz
```
