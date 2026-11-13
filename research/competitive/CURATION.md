# Curation of the competitive history

`results/history.json` is append-only by contract, and that contract was broken once, on purpose.

When the cryptanalysis research moved out of this crate (#668), the 70 rows whose problems were
cipher systems were removed: 42 `poseidon-t2-*-planted` rows and 28 `anemoi64-cico-n*-fcico` rows.
Those rungs left the public corpus (`grobner::external::corpus::ladder`) at the same time, so the
board could no longer state their ideal equivalence across engines. That equivalence is the gate on
publishing a ratio.

The 450 rows remaining after that curation are unchanged, field for field, and in their original
order. No row was added, re-measured or edited. `COMPETITIVE.md` was regenerated from them with
`cargo run --release --example competitive -- --write`.

The complete 520-row history, including the removed rows, is `research/competitive/results/history.json`
at commit `9532a9a2a33fb4943120afdd2ccc2a99bda7eb65`:

```sh
git show 9532a9a2:research/competitive/results/history.json
```

Every row in that file, the removed ones included, still names the commit it was measured at.

PR #665 subsequently appended 100 upper-rung sweep attempts, measured at `19ff732c`,
bringing the retained history to 550 rows without restoring the 70 removed cipher rows.

Issue #520's matched-ISA re-take appends 104 attempts at `c033f027`: Zeebra and
Sagebrush at each of the original 52 public-algebra cells. The preceding 610
records remain unchanged, giving 714 retained attempts. Sagebrush completes 46
cells, stops at the wall limit on four and refuses two positive-dimensional
conversions; Zeebra completes 44, reaches resource caps on six and refuses two
conversions. The [measurement note](../../docs/research/sagebrush-matched-isa.md)
records per-cell historical movement and a separate controlled ISA comparison.

Issue #678 appends two 98-attempt cohorts, at `5b3e6061` and `4a3c5b67`, bringing the history to
910 attempts while preserving the preceding 714 records. Both include complete checked basis
artifacts in `results/groebner-rs-678.json` and `results/groebner-rs-678-v2.json`. The initial
cohort’s supervisor RSS observations can describe startup only; it remains diagnostic evidence,
and the corrected cohort uses an explicitly labeled child kernel snapshot. History regeneration
now preserves RSS provenance and resource-stop text. The [comparison note](../../docs/research/groebner-rs-comparand.md)
records the operating conditions, source identities, admission rules and limitations.


Issue #675 adds a three-rung planted family at `2^64 - 353`, measured at `65f38d4a`
(production source unchanged from `b310c126`). Its 21 recorded outcomes preserve the preceding
1,115 rows exactly and bring the history to 1,136 rows. Zeebra, Groebner.jl, groebner-rs and grobx
complete all three rungs; Singular, msolve and Sagebrush refuse the characteristic. The
[cohort manifest](results/wide-planted-675-board.json),
[complete-basis verification](results/wide-planted-675-verification.json) and
[failed optional-RSS-cap attempt](results/wide-planted-675-capped-failure.json) retain all outcomes
and their limits. The family uses live-oracle provenance because the requested sole-comparand
condition predates the newer wide-field engines. These easy structured inputs establish coverage;
the board rejects their wall ratios as startup dominated.
