# Grobx randomization attribution and exact-acceptance cost (#714)

**Measured at:** `32996435`, reconstructed from base `02b21224` and the SHA-256-bound
[source patch](../../research/grobx-randomization/source.patch.gz). The external engine is
`1854835dbc25f24dc9a9ba017024d5030e99da1c`. [Build identities](../../research/grobx-randomization/builds.json),
[all outcomes](../../research/grobx-randomization/cohort.json.gz), and the
[reproduction contract](../../research/grobx-randomization/README.md) bind the exact inputs,
source/compiler/lock/settings/binaries, flags, seeds and limits.

## Decision

**Defer exact Zeebra integration.** Plain random combinations materially reduce Grobx's work
at GF(2147483647). With its normal signature prefix retained, disabling only that feature makes
process wall **2.64× longer** and matrix kernel products **2.94× larger**. Plain-only controls
isolate a **5.26× wall** and **6.72× product** difference. Signature zero-test wall differences
remain inconclusive here. These are same-prime Grobx effects, not predicted Zeebra gains.

The straightforward native all-row residual audit erases the plain-combination benefit:
its larger-prime process is **1.30× slower than deterministic plain reduction**. The existing
exact-certified objective is much more expensive and changes several algorithmic choices.
Neither establishes a cheap exact acceptance path for an integrated randomized solver.
The retained opt-in research tools change no shipping Zeebra algorithm or API.

## Actual activation and controls

Each source patch gates only plain combinations or signature zero tests. Public
`Params.signatures=false` separately selects plain-only F4. Arithmetic, band eligibility,
ordering, pair criteria and handover policy retain their pinned settings. Disabling plain
combinations inherently removes their band path; this is not a SIMD-only comparison.
Every completed answer matches the complete independently Singular-verified reference basis,
coefficient for coefficient, at its original input digest:

| Corpus | Characteristic | Canonical system SHA-256 |
|---|---:|---|
| `mq-random-10` | 32003 | `16422dafcdb6487ea541f976f7754112b811c85af2b3537ed10fe4ef9c8f3d7f` |
| `mq-random-10` | 2147483647 | `72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2` |

The native-on census includes discarded signature work and final interreduction:

| Field | Signature rounds before restart | Plain combinations | Plain blocks observed | Signature groups tested | Rows ruled zero by signature tests |
|---|---:|---|---:|---:|---:|
| 32003 | 9 | off | 0 | 26 | 27 |
| 2147483647 | 9 | on | 28 | 36 | 32 |

Both normal runs restart from the original generators. No-plain at 32003 preserves the native
371,017,379 matrix kernel products exactly, as expected from the cutoff. Disabling signature
tests removes all observed signature-group events. The runner checks actual reduction modes and
events as well as flag receipts. Native `reduce-by=prime/field` fallback labels predate these
experimental gates; under a disabled gate those labels are not the causal explanation.

## Fresh-process measurements

AMD Ryzen Threadripper PRO 5995WX, CPU 2, one worker, Rust 1.99.1 / LLVM 23.1.1,
release/fat LTO/one codegen unit, matched `x86-64-v3`, upstream allocator on both sides.
Five repetitions per arm and prime, reversing arm/field order on alternate repetitions.
There are 170 primary attempts and 12 separately labelled seed-sensitivity attempts.
Every changed policy has same-binary observer-on/off controls. All 182 completed and verified.

Table entries are **process-wall medians [minimum–maximum], milliseconds**, including parsing,
checking where enabled, and full output encoding. Reference-basis verification follows timing.
These wall comparisons use observer-off policies; work counts below come from their on controls.

| Policy | GF(32003) | GF(2147483647) |
|---|---:|---:|
| Stock native | 360.6 [344.5–370.4] | 164.0 [160.2–186.1] |
| Patched native, observer off | 405.5 [389.1–413.6] | 177.8 [173.6–197.5] |
| No plain combinations | 389.9 [386.4–426.2] | 470.2 [461.6–508.7] |
| No signature zero tests | 401.4 [387.2–432.6] | 199.5 [179.7–203.7] |
| Neither randomized path | 394.9 [384.9–424.4] | 497.6 [450.9–516.9] |
| Plain-only | 296.8 [291.3–321.1] | 66.6 [66.1–73.4] |
| Plain-only, no combinations | 293.6 [290.3–308.8] | 350.8 [341.3–371.1] |
| Plain-only, native residual audit | 619.9 [606.5–673.8] | 455.9 [429.1–472.4] |
| Exact-certified objective | 15,730.1 [15,559.7–17,043.7] | 16,623.1 [15,606.0–17,253.4] |

Native stock versus patched/off costs about 12.5% and 8.4% at these medians: compilation/layout
and policy/observer gates are not free. Native counters-on medians are 429.6 and 187.8 ms,
about 5.9% and 5.6% above patched/off, with overlapping ranges. Every on/off pair retains its
structural path; counter values are stable across its five repetitions. Do not treat noisy
small changes or the observer's point estimates as precise zero-cost overhead claims.
Signature-test wall ranges overlap, so their isolated runtime effect remains **inconclusive**.

Load at attempt boundaries ranged from 1.85 to 6.49 under the declared gate of 8. Other builds
continued; this was not an idle-machine campaign. No further repetitions were added to resolve
noise. Full medians/ranges, sensitivity cases, work census and peak RSS are in
[summary.json](../../research/grobx-randomization/summary.json) and
[summary.csv](../../research/grobx-randomization/summary.csv).

## Work and exact-acceptance cost

Matrix kernel products count executed sparse-support multiplications, including zero band lanes
and combination construction; they include every signature/plain round and final interreduction.
They are not physical bandwidth or a complete count of checker/cofactor arithmetic.

| Policy, observer on | GF(32003) matrix products | GF(2147483647) matrix products |
|---|---:|---:|
| Native | 371,017,379 | 122,327,779 |
| No plain combinations | 371,017,379 | 359,788,914 |
| No signature zero tests | 374,004,721 | 126,949,398 |
| Neither | 374,004,721 | 364,410,533 |
| Plain-only | 288,543,363 | 41,480,363 |
| Plain-only, no combinations | 288,543,363 | 278,941,498 |
| Additional native residual-audit products | 289,749,910 | 283,216,831 |

The native audit reduces **every original matrix row**, including reducer rows, against the final
pivots before the plain batch returns. All observed audits passed. Median measured audit-stage
cost is 321.1 ms and 383.9 ms; this work is inside the same process wall and resource budget.
The larger-prime audited path performs 324,697,194 matrix products in total, exceeding the
278,941,498 of deterministic plain reduction. Its process median is 455.9 versus 350.8 ms.
The smaller-prime audit adds repeated work where plain combinations were already disabled.

Valid pivot formation provides pivot-span inclusion in original-row span; exact zero residuals
supply the reverse inclusion. This is a native invariant audit, not an independent cofactor
certificate. **A failed audit is recorded and refused by the driver after the whole call.**
Transactional per-batch rejection, rollback and retry/fallback are not implemented or costed.
The experiment therefore does not establish a ready exact-mode recovery API.

The independent small-matrix checker additionally requires explicit candidate/input combination
witnesses. Tests reject an omitted pivot, a rogue extra pivot, an invalid witness and incomplete
checks, and cover zero/dependent rows and exhaustive two-by-two transforms over GF(2), GF(3),
and GF(7). Driver tests cover interrupted calls followed by reuse and refuse the audit for
signature-engine requests. A final global span check cannot certify signature-prefix syzygies:
a later high-signature `(1,0)` can mask an incorrectly skipped earlier low-signature `(1,0)`.
A signature-aware validator must check admissible prefixes at the original decision boundary.

Exact-certified mode retains ten signature rounds, disables handover/randomized reduction through
cofactor tracking, and invokes the independent exact checker. Its reported checker-stage medians
alone are about 12.4 and 13.2 seconds, separate from process-wall measurements above. Its peak-RSS
medians are 152.0 and 164.3 MiB, versus roughly 15–16 MiB in raw policies. This changed objective
is not a randomization-off control or a measurement of adding only a checker to a raw result.

## Failure model and literature

The pinned [sampler](https://github.com/code1-de/grobx/blob/1854835dbc25f24dc9a9ba017024d5030e99da1c/src/matrix.rs#L768)
uses nonzero coefficients from multiply-high range reduction. The plain reducer counts **two
total zero combinations**, not two consecutive zeros. Signature groups instead require all their
`s` tested combinations to vanish against unchanged admissible pivots. These are different tests.

[Monagan–Pearce 2017, §2](https://www.cecm.sfu.ca/~monaganm/papers/romanPASCO17.pdf) describes a
consecutive-zero strategy with experimentally chosen square-root block sizes. The previously
unlocated reference is now identified: [Demin 2026, arXiv:2609.14433v1](https://arxiv.org/html/2609.14433v1).
Its Proposition 1 assumes independent uniform full-field coefficients and fixed blocks;
Remark 2 distinguishes total from consecutive zeros. Proposition 3 includes the number of blocks
in parameter selection. Section 3.4 validates the final candidate by an exact Gröbner-basis test
and retries, additionally relying on equality of candidate and input ideals. These results require
adaptation to Grobx's nonzero biased sampler, adaptive blocks and reused streams.

An independent conditional bound uses `Q = 2^64` and maximum atom
`alpha = ceil(Q/(p-1))/Q` **under fresh independent uniform words**. For residual block rank `r`,
conditioning all but `r` independent row coefficients leaves at most one assignment that makes
the combination zero, so its probability is at most `alpha^r`. A nonzero combination lowers
residual rank by one. Summing possible residual ranks `r >= s >= 1` at the two total-zero events
bounds a discarded plain block by
`B2 <= sum(alpha^(r+s)) = alpha^2 / ((1-alpha)*(1-alpha^2))`.
This assumes the documented sequential equivalence of band pivots. A signature group with
unchanged valid pivots instead has bound `alpha^s`.

| Field | Signature `s` | Conditional signature-group bound | Conditional plain-block bound |
|---|---:|---:|---:|
| 32003 | 3 | 3.05e-14 | 9.76e-10, unused because plain combinations are disabled |
| 2147483647 | 2 | 2.17e-19 | 2.17e-19 |

These are ideal-draw bounds, **not guarantees for fixed-seed Xoshiro**. The stream is restarted
from the same draw after handover. A whole-solve bound needs a deterministic event cap or a valid
online risk allocation; an observed event count cannot simply become an unconditional union
bound. Three solver seeds all matched the reference, but finite success is not a soundness proof.

## Outcomes, limitations and continuation gate

All 170 primary and 12 sensitivity attempts completed within 60 seconds/2 GiB per child; the
campaign completed in 644 seconds under its declared 1,800-second outer stop. No final timeouts,
resource refusals or coefficient mismatches occurred. The initial diagnostic run was interrupted
after 18 outcomes: 16 recorded verified, two failed the old report decoder despite completing
with exact certificates. All 18 full answers reverify; their original statuses remain unchanged
in [diagnostic reanalysis](../../research/grobx-randomization/diagnostic-reanalysis.json) and their
timings are excluded from the new medians. The one declared restart corrected that decoder and
streamed large proof payloads through existing lossless storage. No further extension occurred.

The causal plain-combination hypothesis is supported on the larger-prime MQ10 case. The
signature-test runtime claim is inconclusive. The straightforward residual-audit integration is
rejected for these two cases; exact production integration remains deferred. Future work must
establish signature-compatible or final exact acceptance, original-ideal provenance, shared
remaining budgets and bounded fresh-seed retry/deterministic fallback. Neither fallback cost nor
Las Vegas correctness is inferred from successful audit runs. Public Katsura/Cyclic/larger-MQ,
wide-prime and extension-field adoption gates remain unmeasured; no generic algorithm redesign
or production-default proposal is made from this two-input campaign.
