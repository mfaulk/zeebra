# Anemoi: what was taken unchanged, what was verified, and what is a reconstruction dependency

**Measured at:** publication bound `bda7ed44`…`7aa9a9be` for §§1–9 — the commits that published
those figures, recovered from git rather than recorded at the time
([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)). §10's own
figures are at `93898118`, recorded when they were taken rather than recovered. §8a.9's are at
`19ff732c`, and are counts rather than timings — no clock, nothing pinned, reproducible anywhere.

M24-C. The implementation half of candidate 1 of [`additional-benchmarks.md`](additional-benchmarks.md)
§1, which ranks it first of four against a cap of five. This document records the sources actually
read, the oracle each claim rests on, and the one choice that is a convention rather than a
specification.

## 1. The sources, and which URL each was read from

**`eprint.iacr.org` PDF paths return HTTP 403 from this environment** — the same constraint
`additional-benchmarks.md` §8 records. Everything below was read from a mirror that works.

| Source | Read from |
|---|---|
| Bouvier, Briaud, Chaidos, Perrin, Salen, Velichkov, Willems, *New Design Techniques for Efficient Arithmetization-Oriented Hash Functions: Anemoi Permutations and Jive Compression Mode*, CRYPTO 2023 | <https://hal.science/hal-04276646/document> |
| The designers' reference implementation (MIT, commit `3e86ff0c`) | `anemoi.sage` and `constants.py` via `raw.githubusercontent.com/anemoi-hash/anemoi-hash` |
| Koschatko, Lüftenegger, Rechberger, *Exploring the Six Worlds of Gröbner Basis Cryptanalysis: Application to Anemoi*, ToSC 2024 №4, DOI `10.46586/tosc.v2024.i4.138-190` | `tosc.iacr.org` — ToSC is open access |
| The Six Worlds experimental output (MIT, commit `fa056e6f`) | `models.sage`, `anemoi.sage`, `attack.sage` and `results/anemoi_p{18446744073709551263,4294967087,65537}_n1_l1_a3_m{F,P}CICO_o1.txt` via `raw.githubusercontent.com/IAIK/six-worlds-anemoi` |

Both reference repositories are MIT, so their data *may* be redistributed — which the Fukuoka files
cannot be, see [`fukuoka-mq.md`](fukuoka-mq.md) §3. Nothing is copied here that is not cited: the
only committed reference numbers are the four CICO witnesses in `src/grobner/research/anemoi.rs`
and the per-step figures in the registry's `ReferencePoint` rows, each traceable to the `results/`
file named above.

### 1.1 The six results files, pinned by content

`docs/research/external-provenance-policy.md` requires a licence verified from the project's own
files at a pinned commit, and a figure quoted from external data to be traceable to the bytes it
came from. The files themselves are 3.8 MB of verbose Magma logs and are **not** committed — the
figures extracted from them are, in `ANEMOI_{17,32,64}_POINTS`. So the bytes are pinned by digest
instead, all six fetched 2026-11-06 from
`raw.githubusercontent.com/IAIK/six-worlds-anemoi/fa056e6f/results/`:

| file | SHA-256 | bytes |
|---|---|---:|
| `anemoi_p65537_n1_l1_a3_mFCICO_o1.txt` | `4781f28b474e959c6de58b59adab9ce9fd4d8e516982c315dcc949870e92b5d5` | 115 731 |
| `anemoi_p65537_n1_l1_a3_mPCICO_o1.txt` | `6c75c0ec13682c440664531f695d4d9936c2fe6a04b2ce31185f70624a73afb7` | 231 828 |
| `anemoi_p4294967087_n1_l1_a3_mFCICO_o1.txt` | `e2be89f2394a263697bb78e97054582f37302d6ec832e550c655fecc6b80d5f2` | 244 693 |
| `anemoi_p4294967087_n1_l1_a3_mPCICO_o1.txt` | `883397c54eb868d68005a712cf667d350b4445ae6d89b2de70e0f369191b81b2` | 211 731 |
| `anemoi_p18446744073709551263_n1_l1_a3_mFCICO_o1.txt` | `c8ac4bf4241406eb6564503346fa79778cfe3bf05b47f8c3985b68db495a86d6` | 1 716 521 |
| `anemoi_p18446744073709551263_n1_l1_a3_mPCICO_o1.txt` | `f25886c1f71d71c292808624085fddffb2a24de6899bc05f94f96c32f57c205b` | 1 274 621 |

The licence was read in full from the repository's own licence file at that commit. It is at
**`LICENCE`** — British spelling, no `LICENSE`, `LICENSE.md`, `LICENSE.txt` or `COPYING`, each of
which returns 404 — and the file is seven lines: the verbatim MIT permission and warranty
paragraphs under `Copyright (c) 2024 Graz University of Technology`, with no title line and no SPDX
identifier. So the grant is MIT, redistribution of the extracted figures is permitted, and
attribution is carried in each `ReferencePoint`'s `source` field.

The spelling is worth recording rather than silently working around: a licence classifier keyed on
`LICENSE*` finds nothing here, which is precisely the failure mode
`external-provenance-policy.md` §1 was written about. This entry was checked by fetching each
candidate path and reading the one that existed, not by trusting a reported SPDX id.

**The extraction rule, because the two steps come from different lines.** The Gröbner figure is
`Total Faugere F4 time`; the conversion figure is `Total FGLM time` where the log prints it, and
otherwise the `Time:` line closing the `FGLM ORDER CHANGE` block. The `65537` logs omit the former,
and where both appear they agree to 0.01 s. The quotient dimension is `unideg`, which the logs print
for every completed rung and which `Get rep mat (dim: …)` repeats. The pre-existing `2^64 − 353`
figures at `N = 1 … 5` are the **paper's published table** rather than a re-extraction, and are left
byte-identical; the `N = 6` row and both new primes are read from the logs by the rule above.

## 2. What was taken from the reference unchanged

At `ℓ = 1` over an odd prime field, with `QUAD = 2`, `γ = 0`, `β = g` and `δ = g^{-1}`:

- **The round function.** `Anemoi = M ∘ R_N ∘ … ∘ R_1`, `R_i = H ∘ M ∘ (+c_i, +d_i)`. The final,
  degenerate round is a linear layer alone.
- **The linear layer.** The reference builds `M` as `get_mds(F, 1)` — the `1 × 1` identity — followed
  by a pseudo-Hadamard transform `y += x; x += y`. At one column the matrix drops out, so
  `M(x, y) = (2x + y, x + y)`, and its inverse is `x -= y; y -= x`.
- **The open Flystel `H`.** `x' = x − βy²`, `v = y − (x')^{1/α}`, `u = x' + βv² + δ`. Read backwards
  this is the degree-`α` relation `x = βy² + (y − v)^α`, `u = βv² + δ + (y − v)^α`, which is what
  makes Anemoi cheap to arithmetize and is what both polynomial models use.
- **The constants.** `c_j^i = g(π₀^i)² + (π₀^i + π₁^j)^α` and
  `d_j^i = g(π₁^j)² + (π₀^i + π₁^j)^α + g^{-1}`, with `π₀` and `π₁` the first and second hundred
  decimal digits of π after the leading 3, reduced mod `p`. **The indexing was checked against the
  reference rather than inferred from the formula**: `i` is the round and runs from **zero**, `j` is
  the column. So the first round takes `π₀^0 = 1`, whence `c_1 = g + 2^α` in closed form, and at
  `ℓ = 1` the column index is always zero, so `π₁` never enters the arithmetic — a consequence of
  `ℓ = 1`, not a simplification.
- **The exponent.** `α^{-1} mod (p − 1)`, not mod `p`.

Not taken: `get_n_rounds`, the `ℓ > 1` MDS constructions (`M_2`, `M_3`, `M_4`, the circulant case),
Jive, and the sponge. The ladder fixes `N` explicitly and this milestone needs the permutation, not
the hash.

## 3. The one reconstruction dependency: `g`

The paper says only "a generator of the multiplicative subgroup". The reference takes
`F.multiplicative_generator()`, which is Sage's **smallest primitive root** — deterministic, but a
convention rather than a specification. `smallest_primitive_root` reproduces the convention: factor
`p − 1`, then take the least `g ≥ 2` whose order is not a proper divisor.

For `p = 2^64 − 353`, `p − 1 = 2 · 13 · 47 · 15095535248534821` and the answer is **`g = 5`**, hence
`β = 5` and `δ = 5^{-1} = 11068046444225730758`.

This is recorded as a reconstruction dependency and **not** as a gap: once the convention is named
there is nothing left to guess, and §4 confirms the value against committed reference data. It is
also why `Anemoi::derived_digest` exists. A parameter checksum covers `p`, `α`, `ℓ` and `N`; if
`smallest_primitive_root` ever returned something else, every constant would move and the parameters
would be unchanged. That is precisely the failure a parameter digest cannot see, and
`additional-benchmarks.md` §6.3 notes Anemoi needs the pin more than Poseidon does.

## 4. How the permutation was verified, and what the oracle is

`check_polynomial_verification` in the reference repository is the stated oracle, and it needs Sage.
**Sage is not available in this environment.** So the verification was done against something
stronger and already committed: the lexicographic Gröbner bases the Six Worlds logs print after
their FGLM step, which are reference *output* rather than a reference *implementation*.

For `α = 3`, `ℓ = 1`, `p = 2^64 − 353`, model `FCICO`, ordering `o1`, the log prints the complete
lex basis for each `N` it reaches. Two checks were run against it.

**(a) Ideal membership, which needs no roots.** Substitute the lex basis's expressions for every
variable into each `FCICO` generator built from the constants derived here, and reduce modulo the lex
univariate. At `N = 1, 2, 3` all `2N` generators reduce to **zero**. That pins, simultaneously:
`g = 5`, `β`, `δ`, `QUAD = 2`, `π₀ mod p`, the round indexing, `c_1 … c_3`, `d_1 … d_3`, the open
Flystel in both directions, `M` and its inverse, and the final-linear-layer convention
(`final_ll = True`, which the log's own header states).

**(b) CICO witnesses in the permutation's own coordinates.** Root the lex univariate, read each root
back through the basis to the input word `y`, and evaluate the permutation. Four witnesses result,
and they are what `test_the_permutation_matches_the_reference_witnesses` asserts:

| `N` | input `y` | `Anemoi(0, y)` |
|---:|---|---|
| 1 | 8431162935045355170 | `(0, 8504299942464173430)` |
| 1 | 16536366872043122313 | `(0, 10906135472056154455)` |
| 2 | 1761853426583392112 | `(0, 503324230923223481)` |
| 4 | 8251407552160637060 | `(0, 17265183214956306941)` |
| 5 | 8393487001060711113 | `(0, 15310351087790638079)` |

The **count** is checked too, not only the values: the log's own `nsols` line reports 2, 1, 0, 1 and
1 solutions at `N = 1 … 5`, and the root-finding agrees at every rung including the empty one.
`N = 3` contributes no witness because the reference found none either.

And the loop closes without the reference: `examples/anemoi_ladder row anemoi64-cico-n1-fcico`
takes Zeebra's own F4, FGLM and root finding and lands on `8431162935045355170`, the first witness
in the table. That is Zeebra recovering a point the reference's own output determined, through a
completely different pipeline.

**A trap worth recording.** The variable labels in the Six Worlds logs are *positionally permuted*
relative to the model's own names. `models.sage` re-interprets each specialized polynomial into a
fresh ring whose variable list is the fast ordering, and the names bind by position, so the generator
the log prints as `X0100` is the model's `Y0000` — the CICO input. The two orders coincide at `N = 1`
and diverge from `N = 2` on, which is exactly the shape of bug that passes the easiest case. Reading
the logs by label without accounting for this yields points that satisfy no equation.

## 5. The machine-independent invariant — checked, and it agrees

`dim F_p[x]/I` does not depend on the machine, the library or the wall clock, so this is the one
number Zeebra can be right or wrong about without any reference to a clock. A disagreement is a
**defect in Zeebra or in the model, not a performance difference**, and it stops the workstream
rather than becoming a table entry. It is therefore read **first**.

The committed logs report, for `α = 3` and both models, a quotient dimension of `(α + 2)^N` exactly.
Zeebra's own figure, from the leading-term ideal of its degrevlex basis, agrees at every registered
rung in both models:

| `N` | 1 | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|---:|
| `(α + 2)^N` | 5 | 25 | 125 | 625 | 3125 |
| Zeebra, `FCICO` | 5 | 25 | 125 | 625 | 3125 |
| Zeebra, `PCICO` | 5 | 25 | 125 | 625 | 3125 |

**Ten rows out of ten.** Reproduce it with `cargo run --release --example anemoi_ladder dimensions`,
which pins no environment because it needs none. `N = 1 … 4` in both models is also a unit test,
`test_the_quotient_dimension_is_the_published_power`, so a regression fails CI rather than appearing
as a row; `N = 5` is left to the runner to keep the test cheap.

The computation is combinatorial once F4 has finished — the number of standard monomials of the
leading-term ideal — so it costs nothing beyond the basis, which is why it is affordable as the
first check rather than the last.

The published value is tagged `Claim::Observed` and **not** `Claim::Proved`: it is a measurement
from one implementation, and the designers' corresponding statement is a conjecture. Zeebra agreeing
with it does not promote either one to a theorem; it means two independent implementations measured
the same thing.

## 6. The two models, and what the registry had to change

`FCICO` and `PCICO` are from Six Worlds' own `models.sage`, emitted in its `o1` variable ordering —
the ordering every committed `..._o1.txt` log was produced under, and the one that paper reports as
the good one. Zeebra's degrevlex order is induced by the variable *indices*, so the index assignment
**is** the ordering, and matching it is what makes the published per-row figures comparable at all.

| `N` | `FCICO` variables = generators | generator degrees | `PCICO` variables = generators | generator degrees |
|---:|---:|---|---:|---|
| 1 | 2 | `3, 3` | 2 | `3, 2` |
| 2 | 4 | `3, 3, 3, 3` | 3 | `3, 4, 3` |
| 3 | 6 | `3`×6 | 4 | `3, 4, 6, 4` |
| 4 | 8 | `3`×8 | 5 | `3, 4, 6, 8, 5` |
| 5 | 10 | `3`×10 | 6 | `3, 4, 6, 8, 10, 6` |

Both columns agree with the `n_v`, `n_e` and `degs` lines the committed logs print per round count,
which is what `test_the_sizes_match_the_published_logs` and
`test_the_generator_degrees_are_the_published_shapes` assert.

Two things had to change in the registry, and the second is a genuine gap rather than a
convenience.

**The model is inside the identity.** `ChallengeParameters::AnemoiCico` carries it as a field, so it
appears in `canonical_lines` as a `model fcico` / `model pcico` line. Without it, `N = 5` `FCICO` —
ten generators of degree three — and `N = 5` `PCICO` — six of degrees up to ten — would share a
digest, and a comparison tool keyed on the digest would compare them and report nothing wrong.
`test_the_two_anemoi_models_are_different_problems` asserts the separation at every rung.

**`ReferencePoint` is new, and it is where a published competitor figure lives.** `ExternalStatus`
records whether and when a problem was solved elsewhere and carries no time, no memory and no
hardware, so the Six Worlds figures had nowhere to go. A reference point carries source, parameters,
step, reported time, reported memory, hardware and software. Three decisions worth recording:

- **It sits outside `canonical()`**, for the reason programme metadata does: a corrected
  extrapolation must not change which mathematical problem a row is.
  `test_a_reference_point_does_not_change_identity` asserts it.
- **The basis step and the conversion step are separate points, never one combined figure.** The
  whole reason this family was chosen is that they are 2 400× apart at `N = 5`; a single number
  would hide the finding.
- **`reported_memory` is `None` on every Anemoi row, and that is a real answer.** The logs report
  peak resident set size once per sweep — 227 MB for the whole `FCICO` run over `N = 1…8`, 225 MB
  for `PCICO` over `N = 1…7` — so attributing either to one row would be inventing a measurement.

**The class is `Official`, not `FaithfulReduction`.** The combination — reduced round counts of a
real primitive, registered as official — has no precedent in this registry, so: `FaithfulReduction`
means *this registry reduced an official problem*, and its `of` field has to name that problem.
There is none. Nobody posed full-round Anemoi as a challenge and it is not registered, so an `of`
would be a dangling reference. What is published is the ladder itself — Six Worlds ran `N = 1…8` and
reported those rows as its own experiment — so the registered object is the published object.
`ExternalStatus::PublishedWithAnswer` then makes `significance(true)` a `Reproduction`, the
strongest honest claim on a solved reduced instance. The caveat `FaithfulReduction` would have
carried structurally is carried in each row's `notes`: a result at `N = 5` says nothing about
full-round Anemoi, which is 21 rounds at 128-bit security.

`Objective::CicoExact` fits as written and no new objective was added. Anemoi CICO constrains the
**leading** word of a `2ℓ`-word state at each end — `x_in = 0` and `x_out = 0` — which is what that
tag means.

## 7. The field

`p = 2^64 − 353 = 18446744073709551263`. Odd, so `PrimeFieldElement64<P>` holds it in Montgomery
form with no new arithmetic — `montgomery::uses_montgomery` requires only `p % 2 == 1`, and
Goldilocks is already covered at the same width. `Zp18446744073709551263` is the alias, and
`test_multiplication_matches_wide_reduction` now covers this modulus at the boundary values. Nothing
else in `fields` changed.

## 8. The runner, and what has deliberately not been measured

`examples/anemoi_ladder` has three subcommands, and the split between them is the point.

```sh
cargo run --release --example anemoi_ladder list        # the ten rows and their published figures
cargo run --release --example anemoi_ladder dimensions  # the machine-independent gate, §5
ZEEBRA_MACHINE=... ZEEBRA_AFFINITY=... tools/benchlock.sh \
    cargo run --release --example anemoi_ladder row anemoi64-cico-n3-fcico
```

`row` runs F4, then FGLM, then root finding, each timed separately — separately because the
published finding is that the conversion costs 2 400× the basis at `N = 5`, and a combined figure
would hide it — and verifies any recovered point **through the permutation** rather than through the
system that produced it.

**`row` refuses to print a single number unless `ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY` are set**, and
says so with exit code 2. A wall-clock figure from an unpinned environment is not a measurement, and
a figure produced by accident is a figure that gets quoted later. Measurements must additionally be
serialized under `tools/benchlock.sh`, because this box runs several agents at once and a
contended core is a silently wrong figure.

What was established before any clock was read: the quotient dimension at all ten rows, the
generator shapes against the logs, the witnesses, and that the whole pipeline runs end to end. §8a
is the ladder, run in §5's binding order.

## 8a. The ladder, run — and the published wall does not reproduce

`N = 1 … 4`, both models, cores 0–7, `ZEEBRA_MACHINE=fedora ZEEBRA_AFFINITY=0-7`, one row per
acquisition of `tools/benchlock.sh`.

| row | basis | conversion | univariate | total | `D` | witness |
|---|---:|---:|---:|---:|---:|---|
| `n1-fcico` | 51.3 µs | 21.9 µs | 102.8 µs | 176.1 µs | 5 | **verified** |
| `n1-pcico` | 37.3 µs | 19.5 µs | 102.2 µs | 159.1 µs | 5 | **verified** |
| `n2-fcico` | 658.5 µs | 202.5 µs | 391.3 µs | 1.252 ms | 25 | **verified** |
| `n2-pcico` | 278.6 µs | 140.5 µs | 391.9 µs | 811.0 µs | 25 | **verified** |
| `n3-fcico` | 11.479 ms | 5.747 ms | 7.486 ms | 24.712 ms | 125 | none — zero-dimensional, **no base-field point** |
| `n3-pcico` | 884.9 µs | 3.690 ms | 7.384 ms | 11.959 ms | 125 | none — same |
| `n4-fcico` | 477.30 ms | 404.09 ms | 160.39 ms | 1.0418 s | 625 | **verified** |
| `n4-pcico` | 27.04 ms | 293.94 ms | 172.70 ms | 493.68 ms | 625 | **verified** |

Every witness is checked by running the permutation, not the system that produced it. **`N = 3`
returning no base-field point in either model is a prediction that could have failed**: the Six
Worlds logs' own `nsols` line is 0 at that rung, and an implementation subtly wrong about the
constants is far likelier to invent a witness than to agree on an empty set. Both models agree on
`D = 125` there, so the system is zero-dimensional and the absence is about the base field.

### 8a.1 The comparison that survives the hardware gap — and what it is actually measuring

> **Superseded in part by §8a.3.** The ratio-of-ratios below is arithmetically correct and the
> framing is still the right one, but §8a.3 measures the same ladder at two further
> characteristics and shows that most of the gap belongs to the *reference's* field arithmetic
> rather than to this crate's conversion. Two specific claims in this subsection reverse there;
> they are flagged inline. Kept rather than rewritten so that what was concluded from one
> characteristic, and why it was wrong to stop there, both stay readable.

The published figures are Magma on a 2015 Xeon and these are Zeebra on a 2026 workstation, so no
wall-clock ratio between them means anything. **A ratio between two stages of the same run on the
same machine does**, and that is where the published claim lives: "the conversion, not the basis, is
the wall."

| row | Zeebra conversion / basis | Magma conversion / basis | they differ by |
|---|---:|---:|---:|
| `n3-fcico` | **0.50** | 11.7 | 23x |
| `n3-pcico` | **4.17** | 32.0 | 8x |
| `n4-fcico` | **0.85** | 242 | **286x** |
| `n4-pcico` | **10.87** | 284 | 26x |
| `n5-fcico` | **1.71** | 2 367 | **1 382x** |
| `n5-pcico` | **51.0** | 2 731 | 54x |

> **For `FCICO` the published finding is contradicted, not merely attenuated: Zeebra's conversion is
> *cheaper than its own basis* at every rung measured.** For `PCICO` the direction reproduces — the
> conversion does dominate and does grow — but at roughly a twenty-sixth of the published ratio.

The growth rates say where the difference comes from, and it is not all in the conversion:

| `N = 3 → 4` | Zeebra basis | Zeebra conversion | Magma basis | Magma conversion |
|---|---:|---:|---:|---:|
| `FCICO` | 41.6x | **70.3x** | 16.5x | **341x** |
| `PCICO` | 30.6x | **79.7x** | 19.9x | **176x** |

So Zeebra's basis step grows *faster* per rung than Magma's (41.6x against 16.5x) and its conversion
grows *far slower* (70.3x against 341x). The ratio moves by 1.7x per rung here and by 20.7x per rung
there.

> **This conclusion does not survive §8a.3.** Magma's conversion growth of 341x per rung is measured
> at `p = 2^64 − 353`. At `p = 65537` the same Magma, the same machine and the same system give
> 83.7x per rung against Zeebra's 101.8x — so at the small characteristic **Zeebra's conversion
> grows faster than Magma's**, and the sign of this finding is a property of the reference's
> arithmetic path rather than of either conversion algorithm.

**What this does not say.** It does not say Zeebra's FGLM is faster than Magma's; that would be a
cross-machine claim and the stage ratios are deliberately chosen to avoid making one. It does not
say the published figures are wrong — they are measurements of a different implementation, and
`additional-benchmarks.md` §3.2 ranked this family first precisely because its reference point is
raw data rather than a summary. And `D = 625` at `N = 4` is small; nothing here extrapolates past
the rung it was measured at.

### 8a.2 `N = 5`, run as a test rather than a sweep — and the prediction held

`N = 5` is the last rung the published logs report a conversion for, and the one where that
conversion is **6.13 hours**. The prediction was written into the runner script before the run: `D`
goes 625 → 3 125, so a `D³` conversion predicts roughly **50 s** in total for `n5-fcico`.

| row | basis | conversion | univariate | **total** | `D` | witness |
|---|---:|---:|---:|---:|---:|---|
| `n5-fcico` | 26.908 s | **46.07 s** | 4.0 s | **76.96 s** | 3 125 | **verified** |
| `n5-pcico` | 0.695 s | **35.46 s** | 4.21 s | **40.36 s** | 3 125 | **verified** |

Observed 76.96 s against a predicted ~50 s — **1.54x**, and the conversion's own growth was
**114x** against the `D³` model's 125x (and 121x for `PCICO`). So the cost model that produced the
prediction is validated at the rung it was extrapolated to, which is the thing M24 asks for over a
bare benchmark.

Both models recover the **same** witness, `8393487001060711113`, which is the cross-check the two
models exist to permit: same primitive, same solutions, two systems.

| row | Zeebra conv / basis | Magma conv / basis | ratio-of-ratios | conversion wall gap |
|---|---:|---:|---:|---:|
| `n5-fcico` | **1.71** | 2 367 | **1 382x** | 479x |
| `n5-pcico` | **51.0** | 2 731 | **54x** | 439x |

> **At the rung where the published conversion costs 6.13 hours, Zeebra's costs 46 seconds, and the
> recovered witness is checked by running the permutation.**

The wall gap — 479x and 439x on the conversion — is quoted here *with both machines named*
(Magma V2.26-2 on an Intel Xeon E5-2630 v3 @ 2.40 GHz against Zeebra on this workstation, cores
0–7) and is **not** a like-for-like solver comparison. The machine-independent figure is the
ratio-of-ratios, and it is 1 382x for `FCICO`. Even a generous decade-of-hardware factor does not
reach 479x, so the gap is not plausibly hardware alone — but attributing it between the algorithm,
the implementation and the field arithmetic is not something these two columns can do.

**This is the milestone's strongest externally calibrated result, and the first evidence of any kind
about how `fglm` scales against another implementation on the same problem.** It is also the
reverse of what the family was chosen to test: `additional-benchmarks.md` §3.2 picked Anemoi because
the published conversion costs 2 400x the published basis, calling that "the single most useful fact
in this issue" for a crate whose FGLM scalability has its own milestone document. That wall is real
in Magma and does not exist here.

### 8a.3 Three characteristics, and the attribution (#283)

§8a.1 declined to apportion the gap between "the algorithm, the implementation and the field
arithmetic", on the correct ground that two columns measured at one prime cannot do it. The Six
Worlds sweep publishes **the same system at three primes**, so the experiment that can is to hold
`α = 3`, `ℓ = 1`, the model and `N` fixed and vary only the characteristic.

The design rests on one asymmetry. Zeebra's `PrimeFieldElement64<P>` is **one Montgomery path at
all three primes** — `p = 65537` and `p = 2^32 − 209` are const-generic instantiations of the same
code as `p = 2^64 − 353`, which is why #283 needed no new field arithmetic. Magma's is not: its own
log headers say `Matrix kind: Modular FP` at `65537` and `Matrix kind: Generic finite field` at both
larger primes. So a within-implementation ratio is comparable down the column for this crate and is
**not** comparable down the column for the reference — and that non-comparability is the finding.

All figures Zeebra-side are from **one benchlock acquisition** on 2026-11-06,
`ZEEBRA_MACHINE=fedora ZEEBRA_AFFINITY=0-7`, `taskset --cpu-list 0-7`, `-C target-cpu=x86-64-v3`
verified present in the build. Taking all eighteen rows in one session is deliberate: the `N = 5`
figures in §8a.2 were taken weeks earlier and this session's `n5-fcico` basis is 16.97 s against
that section's 26.91 s, so cross-session basis figures are not safe to mix into a three-way
comparison even though the conversions agree to 5%.

#### The quotient-dimension gate, first

Thirty rows, three characteristics, `D` against `(α + 2)^N`: **30 of 30 agree**, at 5, 25, 125, 625
and 3 125. Machine-independent, so this is the check that had to pass before any timing meant
anything.

#### `N = 4`: the one rung where all three primes publish both steps

| `p` | Zeebra basis | Zeebra conv | **Zeebra conv/basis** | Magma basis | Magma conv | **Magma conv/basis** | ratio-of-ratios |
|---|---:|---:|---:|---:|---:|---:|---:|
| `65537` `FCICO` | 0.2966 s | 0.4667 s | **1.57** | 0.049 s | 1.620 s | **33.1** | **21x** |
| `2^32 − 209` `FCICO` | 0.2986 s | 0.4255 s | **1.43** | 0.439 s | 63.229 s | **144.0** | **101x** |
| `2^64 − 353` `FCICO` | 0.2968 s | 0.4161 s | **1.40** | 0.280 s | 67.760 s | **242.0** | **173x** |
| `65537` `PCICO` | 0.0262 s | 0.3315 s | **12.65** | 0.020 s | 1.420 s | **71.0** | **5.6x** |
| `2^32 − 209` `PCICO` | 0.0247 s | 0.3145 s | **12.74** | 0.159 s | 50.279 s | **316.2** | **25x** |
| `2^64 − 353` `PCICO` | 0.0245 s | 0.2950 s | **12.05** | 0.199 s | 56.439 s | **283.6** | **24x** |

Read the two ratio columns against each other:

> **Zeebra's conversion/basis ratio is flat in the characteristic — 1.57 / 1.43 / 1.40 for `FCICO`
> and 12.65 / 12.74 / 12.05 for `PCICO`, a spread of 12% across a 47-bit range of primes. Magma's
> moves by 7.3x and 4.5x over the same three primes. The ratio-of-ratios therefore collapses from
> 173x to 21x, and every bit of that collapse is the reference's column moving while this crate's
> stands still.**

#### `N = 5`, and the wall gap that was the headline

| `p` | Zeebra conv | Magma conv | Zeebra c/b | Magma c/b | ratio-of-ratios | raw conversion gap |
|---|---:|---:|---:|---:|---:|---:|
| `65537` `FCICO` | 47.53 s | 135.64 s | 2.96 | 124.6 | **42x** | **2.85x** |
| `2^64 − 353` `FCICO` | 43.53 s | 22 057.08 s | 2.57 | 2 366.6 | **922x** | **507x** |
| `65537` `PCICO` | 38.19 s | 75.75 s | 58.5 | 587.2 | **10x** | **1.98x** |
| `2^64 − 353` `PCICO` | 34.96 s | 15 569.55 s | 54.6 | 2 731.5 | **50x** | **445x** |

`2^32 − 209` is absent from the conversion column because the sweep ran the `N = 5` basis step
there and stopped; the registry records that as `NOT_REPORTED` rather than as a missing figure.

> **The headline number does not survive the control. The `FCICO` conversion wall gap is 507x at
> `p = 2^64 − 353` and 2.85x at `p = 65537` — same system, same round count, same Magma binary,
> same reference machine. Zeebra's own conversion moved 9% across the two primes (43.53 s → 47.53 s,
> and the *larger* prime is the faster one). At 2.85x, against a 2014 Xeon E5-2630 v3 @ 2.40 GHz
> from a 2022 Threadripper, the measured difference is inside what a decade of hardware explains on
> its own.**

This is the result that favours the crate least, and it is stated first for that reason.

#### The verdict on the three candidates

**(1) Faster arithmetic on the 64-bit prime — supported, and it is the dominant term.** But the
sharper form is the reference-side one: it is not that Zeebra is unusually fast at 64 bits, it is
that **Magma is unusually slow there**. Magma's `FCICO` `N = 5` conversion is 163x cheaper at
17 bits than at 64 bits (135.64 s against 22 057.08 s) while its basis step is only 8.6x cheaper;
Zeebra's conversion is flat to within 9%. And the mechanism is named in the reference's own log
header rather than inferred — `Modular FP` at `65537`, `Generic finite field` at `2^32 − 209` and
`2^64 − 353`. The cost cliff sits at the `65537`→`2^32 − 209` boundary and not at 64 bits: the
`N = 4` conversion is 1.62 s, 63.23 s and 67.76 s down that column, a 39x step and then 7%. A
`Modular FP` path whose products must stay exact in a double's 53-bit mantissa cannot be entered
above about 26 bits per operand, which is consistent with where the step appears.

**(2) FGLM genuinely scaling better — ruled out at the strength §8a.1 implied, and the growth
comparison reverses.** At `p = 65537` Magma's `FCICO` conversion grows 83.7x from `N = 4` to
`N = 5` and Zeebra's grows 101.8x. §8a.1's "Zeebra's conversion grows far slower — 70.3x against
341x" is an artefact of reading growth at the one prime where Magma's arithmetic path inflates it.
A residual advantage at the control characteristic is not excluded — 2.85x and 1.98x are in
Zeebra's favour — but it is the size of the hardware gap, so **these data do not establish an
algorithmic advantage, and the earlier text that read as though they did has been marked.**

**(3) Magma's `Variety` computing more than a lex basis — ruled out, and the logs say what it does
instead.** The published figures are of Magma's order-change step alone: the logs delimit
`FGLM ORDER CHANGE` and report `Total FGLM time`, with the univariate solve timed separately under
`UNIV SOLVING` (2.36 s at `N = 5`, `FCICO`, `2^64 − 353`). So nothing extra is folded in. What the
step *is* comes out of the `65537` `N = 6` breakdown, which is the only rung verbose enough to
show it:

| Magma FGLM sub-step, `p = 65537`, `N = 6`, `FCICO` | elapsed | share |
|---|---:|---:|
| `Get rep mat (dim: 15625)` | 13 208.46 s | 56.6% |
| Keller-Gehrig matrix (the spin) | 9 339.52 s | 40.0% |
| kernel for the minimal polynomial | 364.99 s | 1.6% |
| relations for all variables | 427.11 s | 1.8% |
| **total** | **23 340.22 s** | |

Magma spends 97% of its conversion building a `D × D` representation matrix and running a dense
Keller-Gehrig matrix-power spin. Zeebra spends 84–94% of its conversion in the **lex walk**
(§8a.4). Those are two different algorithms for one specification, which is a more useful finding
than either being "faster": it says the two implementations are not on the same cost curve at all,
and that a ratio between them is not a measurement of FGLM.

#### What would actually settle it

A same-machine, same-field comparison. Two are now reachable and neither was when §8a.1 was
written:

- **msolve 0.11.0**, provisioned at `/home/mfaulk/.local/opt/zeebra-ext/bin`. Its modular path wants
  a prime under `2^31`, so it runs at `65537` and `2^32 − 209` and cannot run at `2^64 − 353` —
  which is precisely why #283's control characteristic is the one that can carry a head-to-head.
  `anemoi_ladder msolve <id>` emits the row in msolve's input format for exactly this.
- **A currently maintained Magma on this machine.** None is installed, and until one is, no
  statement in this document is a claim about Magma-as-shipped-today. Magma V2.26-2 is from 2021.

**The msolve run has since been done — see §8a.7, and it settles (2) against this crate.** The
honest summary is now: the published 2 400x conversion/basis ratio is mostly an artefact of the
reference's generic finite-field arithmetic at `p ≥ 2^32`; this crate's conversion is
characteristic-flat where the reference's is not; and against a modern implementation on this
machine at the control characteristic, **this crate's conversion is 21–35x slower, not faster**.

### 8a.4 The `N = 5` footprint, measured

#286 needs an extrapolation to `D = 15 625`, and an extrapolation from a *time* model is not enough
when the question is memory. So the runner now reports what the conversion actually holds, counted
the three ways `FglmMemory` distinguishes — entries are mathematical nonzeros, cells are allocated
field-element slots, bytes are what the allocation takes — beside the process's own peak.

`FCICO`, `p = 2^64 − 353`, `N = 5`, `D = 3 125`:

| quantity | value |
|---|---:|
| operator entries | 12 602 286 |
| operator cells | 12 602 286 |
| operator bytes | 0.150 GiB |
| dense columns, of `N·D = 31 250` | 3 444 (11.0%) |
| span cells | 9 768 750 |
| accepted-vector cells | 9 765 625 |
| dense-block bytes | 0.146 GiB |
| **estimated total** | **0.296 GiB** |
| span row operations | 4 912 340 |
| process peak RSS | 0.324 GiB |
| F4 peak live nonzeros | 1 543 889 |

The estimate and the process measurement are 0.296 GiB against 0.324 GiB, so at this rung the
representations are essentially the whole footprint and `FglmMemory` is not missing anything large.
They are **not** interchangeable in general and are reported side by side for that reason.

Where the conversion's time goes, with `measure_stages` on:

| stage | `FCICO` share | `PCICO` share |
|---|---:|---:|
| quotient basis | 0.0% | 0.0% |
| border classification | 0.0% | 0.0% |
| normal forms (scalar) | 0.0% | 0.0% |
| border symbolic (batched) | 16.7% | 7.5% |
| column assembly | 0.5% | 0.1% |
| **lex walk / dependence** | **82.8%** | **92.3%** |

> **On a cryptanalytic system the dominant conversion stage is the lex walk, not border reduction.**
> `MILESTONE-FGLM-SCALABILITY.md` §9.4 found the dominant stage to be input-dependent — batch
> closure on katsura/cyclic, the lex walk on the systems that scale, 69% on planted-10. Anemoi is
> the first *cryptanalytic* system to go through that split, and it lands at the far end of it:
> 82.8% and 92.3%, above planted-10's 69%. The share also rises monotonically with the rung
> (56.7% → 74.2% → 82.8% for `FCICO` at `N = 3, 4, 5`), which is what an `O(D³)` dependence test
> against an `O(D²)`-ish border does.

> **Corrected under #224.** This paragraph said: "Sparse FGLM attacks the operator construction;
> here the operator construction is 16.7% and falling. Nothing in §8.5's three measurements is
> contradicted." **The first sentence has it backwards, and the error reverses the argument.** Sparse
> FGLM replaces the dense **dependence test** — the 82.8% — with a scalar Krylov sequence plus
> Berlekamp–Massey; it does not make the operator cheaper to build. `src/grobner/fglm/shape.rs`'
> module doc, `MILESTONE-FGLM-SCALABILITY.md` §8.5 answer 5 and `msolve-implementation.md` §3 all say
> so, and §8.5's first measurement is the same statement from the other side: 96% of katsura-7's
> conversion is border reduction, "which sparse FGLM does not touch". On Anemoi that untouched
> remainder is 82.8%, which is why `wiedemann-krylov.md` §2.3 and #368 call this split "the opposite
> split, and the only reason this family qualifies at all".
>
> So this split **does** contradict §8.5's first measurement as a general claim, and narrows it to the
> small-`D` regime it was measured on — §9.4 puts the crossover between `D = 64` and `D = 156`.
> §8.5's no-go on a sparse-FGLM milestone nonetheless stands, for a different reason —
> [`order-conversion.md`](order-conversion.md) §5.B and §7, from eprint 2025/814's Table 7, where
> SparseFGLM fails at `d_I = 5^8` and Wiedemann returns.

What this split does establish is that **the stage a conversion spends its time in is an input
property**, not a property of FGLM: 16.7% border here against §9.4's 43–52% on katsura, and falling
with the rung in both models. An alternative that attacks border reduction is therefore pointed at
the small half on this family, and `MILESTONE-FGLM-SCALABILITY.md` §6.8 has already closed the one
such proposal (#167) on its own measurements.

### 8a.5 `N = 6`: the budget, the ceiling, and the decision

**The criterion, written before the numbers were computed.** Go if the extrapolated conversion wall
is **≤ 2 h** and the extrapolated peak RSS is **≤ 64 GB** — the standing resource gate. No-go, and
report back for authorization rather than launch, if either is exceeded. A run that trips its own
`timeout` is reported as a resource-limited result and not as a failure of the method.

**The extrapolation, from measured storage growth rather than from the `D³` time model.**
`FglmMemory::dense_blocks_for::<F>(15625)` is exact, since both dense blocks are functions of `D`
alone: 244 156 250 span cells + 244 140 625 accepted-vector cells = 488 296 875 cells, **3.64 GiB**
at 8 bytes a cell. That is 25x the `N = 5` figure, as `D²` requires. The operators are the part that
has to be extrapolated: entries went 590 943 → 12 602 286 from `N = 4` to `N = 5`, **21.3x**, so
`N = 6` projects to ≈ 268 M entries, and at the measured 12.8 bytes an entry ≈ **3.4 GiB** for
`FCICO`. `PCICO` is far lighter on the operators — 168 250 → 3 813 032, 22.7x, projecting ≈ 86 M
entries ≈ **1.1 GiB** — and identical on the dense blocks, because `D` is the same 15 625 in both
models. F4's own peak is not the constraint: peak live nonzeros grew 10.3x then 7.5x for `FCICO`,
projecting ≈ 11.6 M ≈ 0.19 GiB.

| model | dense blocks | operators | F4 | **projected total** | projected conversion wall |
|---|---:|---:|---:|---:|---:|
| `FCICO` | 3.64 GiB | ≈ 3.4 GiB | ≈ 0.19 GiB | **≈ 7.2 GiB** | ≈ 1.6 h, plus ≈ 16 min of basis |
| `PCICO` | 3.64 GiB | ≈ 1.1 GiB | ≈ 0.31 GiB | **≈ 5.1 GiB** | ≈ 1.2 h, plus ≈ 16 s of basis |

The conversion walls use the **measured** per-rung growth rather than `D³`'s 125x: 101.8x for
`FCICO` and 115.2x for `PCICO` from `N = 4` to `N = 5`.

> **A correction to the basis figure in the row above, kept rather than quietly fixed.** The
> `FCICO` basis estimate was first computed as "≈ 16 min" from a 57x-per-rung growth factor. The
> **measured** `N = 4 → 5` growth is 54x (0.2966 s → 16.05 s), which gives **≈ 14.5 min**. The 57x
> was not measured — it was carried over from a recollection of the figure.
>
> It does not move the go/no-go: 1.6 h of conversion plus 14.5 minutes is still 1.9–2.2 h and still
> straddles the gate. It is recorded because it is **the same class of error this document charges
> #286's premise with** — a number used in a cost model that nothing had measured. A milestone that
> documents other people's unmeasured-quantity predictions has to document its own, and the fix is
> cheap only because the estimate happened to be close.

**Note what `FglmOptions::recommended()` would do here, and why it is not a surprise.** `D = 15 625`
exceeds `max_quotient_dimension` of 4 096, and the dense blocks' 488 M cells exceed
`max_span_entries` of 20 M by 24x. All four budgets are checked from `D` before any allocation, so
the default would return `SpanStorageExceeded` in milliseconds. `N = 5` fits with 465 625 cells of
the 20 M to spare — it only just fits. So the runner now computes the dense-block figure from `D`
before converting, prints it, and says explicitly when it has lifted the budgets and what it is
betting it can hold. Lifting them uses `unbounded()` with `BatchedBorder` and `Adaptive` set back by
hand, because `unbounded()` deliberately resets the strategies to the reference ones and a
measurement that silently also changed strategy would not be a measurement of this configuration.

**The decision, applying the criterion.**

- **`PCICO`: GO.** 1.2 h against a 2 h budget and ≈ 5.1 GiB against a 64 GB ceiling. Wall budget set
  to **5 400 s**, RSS ceiling **16 GiB** — four times the model, so a trip means something
  unmodelled rather than a slightly pessimistic estimate.
- **`FCICO`: NO-GO on this agent's own authority; run under an explicit integration-agent
  authorization.** 1.6 h of conversion plus ≈ 14.5 minutes of basis is 1.9–2.2 h, which straddles
  the 2 h gate rather than sitting inside it, so it was not launched on the measuring agent's
  judgement.

  **Who authorized it, exactly.** The **integration agent for milestone M25**, acting as integration
  owner. **Not the repository owner**, who was not consulted and has not approved this run. The
  distinction is recorded because a document this careful about provenance should let a reader see
  who decided what, and because an agent-to-agent authorization is a work direction rather than an
  owner's consent.

  **The three conditions, all recorded before the launch.** A **hard external watchdog at 2.5 h**
  (`timeout --signal=INT --kill-after=60s 9000`), killed rather than extended if it reaches the
  backstop and **not** raised mid-run on the strength of apparent progress. The same **16 GiB** RSS
  ceiling, enforced by a polling guard that signals the run rather than by inspection afterwards —
  see below for how that guard was wrong the first time. And the result recorded whatever it is.

  **The authorizing reasoning, so it can be audited and overturned rather than taken on trust.**
  §9's threshold is written as "approximately 2 hours" and the plan states these are *operating
  safeguards, not claims about workstation capability*, so 1.9–2.2 h sits inside the approximation
  rather than past it. The gate's purpose is the sentence beside it — never run an unbounded
  computation because a predictor indicates it might finish — and this run is bounded by a watchdog
  that kills rather than extends, observed at 4.53 GB against a 16 GiB ceiling on a machine with
  ~450 GB free, and killable at any instant. And §8a.6 moves this row from a produced figure to a
  **reproduction** against a published 23 340.220 s, which the authorizing agent stated was the
  decisive factor: the same cost would **not** have been authorized for a produce-only run.

Taking `PCICO` first inverts the brief's stated order, and the reason is that the measurement says
so: both models reach the **same** `D = 15 625` conversion, which is the quantity #286 is about, and
`PCICO` reaches it for a third of the wall and two-thirds of the memory. `PCICO` at `p = 65537` is
also the more valuable of the two rows, for a reason the issue did not know about — see §8a.6.

#### The gate failed first, and the gate was wrong

Before any of the above could be timed, §5's invariant had to be checked at `N = 6`. It **failed**:
all three `PCICO` rows reported **positive-dimensional** against a published `D = 15 625`. Under
§5's rule — "a disagreement stops the workstream" — that halted the timing.

It was not a disagreement. The `Dimension` visitor read

```rust
let basis = basis.ok()?;                      // F4's Result<_, F4Error>
let dimension = series.quotient_dimension(&leads).ok()??;
```

so an F4 **resource refusal** and a genuinely infinite quotient both arrived at the caller as
`Ok(None)`, and the caller printed `Ok(None)` as `positive-dimensional`. **A budget being crossed
was being reported as a mathematical property of the ideal** — on the one check in this document
whose whole purpose is that a disagreement means a defect.

Fixed by giving the outcome three cases instead of two, and by naming the evidence in each. The
positive-dimensional branch now lists the variables with no pure power among the leading monomials,
which is exactly the condition `socle_degree_bound` returns `None` on, because "positive-dimensional"
on a row whose reference publishes a finite `D` does not say whether the generator is wrong or the
basis is incomplete, and the missing pure powers point at which. With that in place the real message
appeared:

```
F4 refused: 20000112 live nonzero entries were needed, over the limit of 20000000
  -- after 41 batches at pair degree 13, peak live nonzeros 13455539
```

**`max_live_nonzeros` crossed by 112 entries in 20 million — one part in 180 000.** And lifting it
alone would have changed nothing, because `F4Options::live_entry_limit` is the *minimum* of
`max_live_nonzeros` and `max_live_bytes / 16`, and the default 320 MB divides to exactly the same
20 M. Both are lifted from the caller, for `N >= 6` only, so §8a.3's `N <= 5` figures stay
reproducible from the same binary: a budget that never binds does not change a result, but a run
taken under different options is not the same measurement and should not look like one.

With the budget lifted, the gate is green:

| row | variables | observed `D` | published `D` | agrees |
|---|---:|---:|---:|---|
| `anemoi64-cico-n6-pcico` | 7 | **15 625** | 15 625 | yes |
| `anemoi32-cico-n6-pcico` | 7 | **15 625** | 15 625 | yes |
| `anemoi17-cico-n6-pcico` | 7 | **15 625** | 15 625 | yes |

`5^6` exactly, in all three characteristics — and at `p = 65537` that is agreement with a number the
reference *prints* (`unideg = 15625`, `Get rep mat (dim: 15625)`) rather than with a formula. 36 of
36 registered rows now agree with `(α + 2)^N`.

#### The RSS guard was watching the wrong process

The `FCICO` authorization is conditional on an enforced memory ceiling, so it is worth recording
that the first guard written for it **could not have enforced one**. It selected the process to
watch with `pgrep -f "examples/anemoi_ladder row $id"`. A heredoc puts the whole launching script's
text into the wrapper's `/proc/<pid>/cmdline`, so that pattern matches the *wrapper* on its own
payload — two `bash` processes at ~4 MB — and does not match the binary at all:

```console
$ pgrep -f "examples/anemoi_ladder row anemoi17-cico-n6-fcico"
  pid=3131927 rss=3992kB comm=bash
  pid=3132014 rss=2492kB comm=bash      # and the real binary is absent

$ pgrep -x anemoi_ladder
  pid=2885645  ./target2/release/examples/anemoi_ladder row anemoi17-cico-n6-pcico
```

A guard reading those wrappers' `VmHWM` would never fire however much the binary allocated. It was
safe only by accident — 4 MB cannot cross a 16 GiB ceiling — which means the run would have
proceeded **unsupervised while looking supervised**. The same pattern also made this document's
author report a queued run as started. Both are #328; the fix is to match the process *name* and
then confirm identity from `cmdline`.

Recorded here rather than only in the issue because §9's resource policy authorizes long runs *on
the strength of* an enforced ceiling, and an authorization is only as good as the instrument behind
it.

**So the binding constraint at `N = 6` is F4, not FGLM.** #286 was scoped on the expectation that
the FGLM budgets were the gate; they are the *second* gate. The conversion pre-flight in §8a.5 was
necessary and not sufficient, and an estimate that had only modelled the conversion would have been
confidently wrong about why the rung was unreachable.

> **The budget named in the quoted message is no longer the one that binds, and the 112 figure was
> never the peak.** #575 moved `F4Options::default()` on 2026-11-08 and the stage within F4 moved
> with it; the real peak is 1.20x the budget rather than one part in 180 000 over it.
> [§8a.9](#8a9-the-binding-budget-re-attributed--and-it-is-a-property-of-the-configuration-323)
> re-measures all of it and is the live record. The paragraph above is kept because the reasoning
> it corrects is #286's and still worth reading.

### 8a.6 `N = 6` is a reproduction at `p = 65537`, not only a produced figure

#286 was filed as "`N = 6`, the rung where the reference has no conversion figure", and §9 of this
document said the logs "stop reporting it after `N = 5`". **That is true at `p = 2^64 − 353` and
false at `p = 65537`.** The `65537` logs run `N = 6` to completion in both models:

| `p = 65537`, `N = 6` | Magma basis | Magma conversion | `D` from the log |
|---|---:|---:|---:|
| `FCICO` | 45.930 s | **23 340.220 s** | `unideg = 15625` |
| `PCICO` | 1.560 s | **11 775.430 s** | `unideg = 15625` |

Two consequences. First, the quotient-dimension invariant has a published value to be gated
against at `N = 6`: `5^6 = 15 625`, printed by the reference itself, so the gate is a comparison
rather than a self-consistency check. Second, `N = 6` at `65537` is a **reproduction** target, which
is a stronger kind of result than the produced figure #286 was scoped for — and it is the row where
a same-machine msolve run is also possible.

At `p = 2^64 − 353` and `p = 2^32 − 209` the position is as #286 described: a published basis figure
and no conversion. A Zeebra conversion there is a **produced** number. It must not be presented as
evidence that this crate outperforms a currently maintained Magma, because no such measurement
exists on this machine and Magma V2.26-2 is from 2021. The registry records the distinction in the
data: `NOT_REPORTED` is prose rather than a quantity, so a tool that parses `reported_time` as a
time cannot read a missing figure as a zero.

### 8a.7 The same-machine comparand: msolve 0.11.0, and it is 21–35x faster

§8a.3 said a same-machine, same-field comparison was what would settle whether any of the residual
belongs to the conversion algorithm. msolve 0.11.0 was provisioned on this workstation while #283
was being measured, so it was done.

**msolve cannot run at `p = 2^64 − 353`** — it refuses with `characteristic must be 0 or < 2^31`,
which is why the control characteristic is the one that can carry a head-to-head at all, and is a
second independent reason #283's design was the right one.

`anemoi_ladder msolve <id>` emits a row in msolve's input format from the same
`instance.system::<N>()` the timed runs use, so both engines are given byte-identical generators.
msolve on **one core** (`taskset --cpu-list 0`, `-t` defaulting to 1), Zeebra on **eight**, both at
`p = 65537`, both under `benchlock`:

| row | msolve total | msolve peak RSS | Zeebra total | Zeebra conversion alone | Magma total (2014 Xeon) |
|---|---:|---:|---:|---:|---:|
| `n3-fcico` | 0.01 s | 7 MB | 17.2 ms | 6.1 ms | 0.067 s |
| `n3-pcico` | < 0.01 s | 8 MB | 5.6 ms | 4.0 ms | 0.050 s |
| `n4-fcico` | 0.04 s | 9 MB | 0.771 s | 0.467 s | 1.709 s |
| `n4-pcico` | 0.03 s | 9 MB | 0.366 s | 0.332 s | 1.480 s |
| `n5-fcico` | **1.81 s** | 32 MB | **63.71 s** | 47.53 s | 136.8 s |
| `n5-pcico` | **1.85 s** | 34 MB | **39.0 s** | 38.19 s | 75.96 s |
| `n6-pcico` | **340.66 s** (re-taken) | 635 MB | **4 248.6 s** | 4 226.5 s | 11 777.0 s |

> **msolve solves `N = 5` end to end in 1.8 s on one core and 32 MB. Zeebra takes 63.7 s on eight
> cores and 330 MB — 35x the wall for `FCICO` and 21x for `PCICO`, and 10x the memory. Same machine,
> same prime, same generators.**

msolve independently confirms the quotient dimension at every rung — 125, 625, 3 125, and 15 625 at
`N = 6` — which is a third witness to §5's invariant beside this crate and the reference. That
confirmation is **not** affected by the withdrawal below: a quotient dimension is not a timing.

#### One withdrawn figure, and why it was re-taken rather than caveated

The first `n6-pcico` msolve measurement read **353.88 s** (scalar sequence 349.52 s of it). It was
taken under `benchlock`, 18:58:50 → ~19:04:44 — but a **stray 32-worker job from another agent ran
outside the lock, ~19:00–19:05**, overlapping nearly the whole measurement. A 32-worker neighbour
takes cores, memory bandwidth and the all-core turbo budget simultaneously, which is the one
contamination mode a wall-clock figure cannot be corrected for after the fact.

So the figure was **withdrawn, not annotated**. It was a comparand for a reproduction of a published
Magma number, and a contaminated comparand is worse than no comparand: it would have made the
reproduction look validated against something that was not measured under the stated protocol.

**The clean re-take is 340.66 s** against the contaminated 353.88 s — the stray neighbour cost
**3.9%**. Small, and that is the point worth recording: a 3.9% error is far too small to notice by
inspection and far too small for any plausibility check to catch, which is exactly why the
correction had to come from the lock log rather than from the number looking wrong. Had the overlap
been reported less promptly, the contaminated figure would have been indistinguishable from a clean
one. The sub-stage split moves the same way and in the same proportion: scalar sequence 337.39 s of
340.66 s, **99.0%**, against 349.52 s of 353.88 s before.

**What the window does and does not touch.** The stray job was 19:00–19:05. From
`$HOME/.zeebra/benchlock.log`:

| measurement | lock window | contaminated? |
|---|---|---|
| the 18-row three-characteristic ladder (§8a.3) | 18:32:14 → 18:37:19 | **no** |
| msolve at `N = 3, 4, 5`, both primes (§8a.7) | 18:48:26 → 18:48:57 | **no** |
| msolve at `N = 6` `PCICO` | 18:58:50 → 19:08:50 | **yes — withdrawn** |
| Zeebra `N = 6` `PCICO` (§8a.8) | started 19:08:50 | **no**, started after the stray ended |
| Zeebra `N = 6` `FCICO` (§8a.8) | queued 19:17:34 | **no** |

Every headline figure in §8a.3 and §8a.7 — including the 1.81 s and 1.85 s that carry the
competitive finding — sits in windows that do not intersect the stray run. The 31-second window for
the eight small msolve rows is the reason: they were cheap enough to be long finished before the
stray job began.

**This settles §8a.3's candidate (2) against this crate, and it should be read as a competitive
result rather than only as an attribution.** There is no algorithmic advantage in this crate's
conversion to be found. The apparent 507x advantage over the published Magma figure was the
reference's arithmetic path; against an implementation whose arithmetic is not the bottleneck the
direction reverses hard. §8a.1's favourable reading was an artefact of having exactly one comparand,
measured at exactly one characteristic, on hardware a decade removed — which is to say it was an
artefact of not having run the control.

Stated as plainly as it deserves, because the temptation with a result like this is to soften it:

> **Zeebra's order conversion is roughly one and a half orders of magnitude slower than msolve's on
> this family, and uses ten times the memory, on the same machine at the same characteristic with
> byte-identical generators. This is a row where this crate loses, and it is the cleanest
> comparable measurement M25 has produced.** It is recorded in #263's competitive report as such.

The bound is deliberately an order-of-magnitude one. Six rows at one prime and three round counts do
not support a tighter claim than "~21–35x end to end, ~30x on the conversion stage", and the ~280x
per-core figure that follows from msolve using one core against this crate's eight is only
defensible for the conversion stage, which is single-threaded here — about one CPU-second per wall
second during the `N = 6` run. Quoting the per-core number without that caveat would overstate it.

**What is measured and what is not.** msolve refuses `p = 2^64 − 353` outright, so every figure here
is at the 17-bit control prime. Whether the same deficit holds at 64-bit characteristic is
**unmeasured**. This crate's conversion being characteristic-flat to 12% is weak evidence that it
would, and that is an inference rather than a measurement. Verified at `N = 4`, `N = 5`, and `N = 6`
`PCICO` for msolve; nothing extrapolates to `N = 7` or to `α ≠ 3`.

The reason is visible in where each engine spends its conversion, and the three do not agree:

| engine | dominant conversion stage | share |
|---|---|---:|
| Zeebra | lex walk / dependence test | 82.8% (`FCICO`, `N = 5`) |
| Magma V2.26-2 | `Get rep mat` + Keller-Gehrig spin | 96.6% (`FCICO`, `N = 6`, `p = 65537`) |
| msolve 0.11.0 | scalar sequence (Wiedemann) | 1.45 s of 1.6 s (`FCICO`, `N = 5`) |

Three implementations, three different dominant stages, one specification. **A conversion ratio
between any two of them is not a measurement of FGLM**, and that is the most transferable thing
#283 produced.

### 8a.8 `N = 6`, attempted — two outcomes, and one of them is not a result

Recorded in the order they happened, including the two that produced no figure, because a
resource-attributed failure is a completed research decision and an infrastructure loss is not one.

All figures in this subsection are from a binary built from the tree at **`f4cb0da`**, which
includes **#305**. That is a different build from §8a.3's `N ≤ 5` column (commit `eb79e05`,
pre-#305). The branch was later rebased past `f4cb0da` to pick up an unrelated upstream test fix,
and the binary was deliberately **not** rebuilt: nothing between `f4cb0da` and that point touches
`grobner/f4/`, `grobner/fglm/` or `poly/`, so the build stays representative of the solver code and
rebuilding would have swapped the binary under a queued measurement for no gain. Stated rather than
left implicit, because "built at `f4cb0da`, source at a later commit" is exactly the kind of
mismatch that is invisible afterwards. #305 bounds symbolic preprocessing's
monomial queue by the symbolic closure, and the first `FCICO` refusal below was *on that structure*,
so the two are not mixable and the `N ≤ 5` basis figures would need re-taking before any
cross-rung basis comparison. The conversion figures are unaffected — #305 is an F4 change.

#### Attempt 1, `FCICO`: refused in 3.8 s, on the third budget of four

```
| grobner | 3.813820931s | did not complete: symbolic preprocessing needed
                            more than the 200000 rows allowed |
```

`F4Error::TooManyRows`, not a memory refusal and not the conversion. §8a.5's pre-flight had lifted
`max_live_nonzeros` and `max_live_bytes`; it had not lifted `max_matrix_rows`, because nothing had
yet crossed it. **Three of F4's four relevant budgets were discovered by separate refusals rather
than by reading the struct**, which is #322's complaint with a third instance.

**The comparison this produced is a competitive result, and must not be fixed away by raising a
constant.** The published Magma run on **this exact row** peaks at **173 808 × 189 401** — *inside*
the 200 000 default that Zeebra refused on. Same system, same model, same round count, same
characteristic. So:

> **For a problem Magma reduces within a 173 808-row matrix, this crate's symbolic preprocessing
> enumerates more than 200 000 rows. That is a measured difference in preprocessing selectivity
> between two F4 implementations, not a budget-tuning problem.** The 200 000 default is not
> obviously the wrong size for a library — Magma fits under it on this row — so raising it is a
> workaround that lets the measurement proceed and leaves the difference in place.

It belongs in #263's gap map on that basis, beside the conversion deficit in §8a.7, and the two are
independent: §8a.7 is an FGLM result and this is an **F4** one. Neither follows from the other.

Two caveats on how far it generalizes. The row counts are not strictly like for like — Magma's
figure is the peak *reduced matrix* it reports, and Zeebra's is the row set symbolic preprocessing
enumerated before reduction, so part of the gap may be a counting convention rather than selectivity
and the honest claim is a one-row observation rather than a ratio. And it lands on exactly the
structure #305 has just bounded, which is why the re-attempt is on a post-#305 build: the figure may
well move, and if it does, that is #305 earning its keep rather than this finding evaporating.

#### Attempt 1, `PCICO`: lost to infrastructure at 3 177 s of 5 400 s — **not** a result

The run reached 3 177 s of its 5 400 s budget at a flat 4.53 GB and was then killed — **not** by its
watchdog, **not** by its RSS guard, and not by any resource limit. The harness stopped the
background shell that had launched it and took the whole process tree with it: `benchlock`,
`timeout`, `taskset` and the binary. `benchlock.log` records `END pid=2761621` at 20:01:47 with a
clean status, so from the lock's point of view the measurement simply finished, and the output file
holds the eleven header lines and no stage table.

**This is categorically not a resource-attributed failure and must not be recorded as one.** It
says nothing whatever about whether `D = 15 625` is reachable; it says a measurement was coupled to
the lifetime of the thing that started it. The fix is `setsid`, so the run becomes its own session
leader and survives its launcher. Recorded because an unbounded-compute policy is only as good as
its ability to tell "the budget stopped it" from "something unrelated stopped it", and these two
look identical in the lock log — the second is the one that silently wastes an hour of a serialized
mutex and reports success.

#### Attempt 2, both models, on the post-#305 build and detached

Re-queued `PCICO` first then `FCICO`, each acquiring `benchlock` separately so the queue interleaves
between them, both under `setsid`, with all four F4 budgets lifted for `N >= 6`, the 2.5 h backstop
on `FCICO` and the corrected RSS guard. Ordering deliberately puts both behind the fourteen jobs
already waiting: a milestone's Minimum criteria are worth more than a Strong-criteria refinement,
and `PCICO` alone already yields the reproduction, the `D = 15 625` check and the conversion figure.

**`PCICO` completed, with a witness.** `p = 65537`, `N = 6`, `D = 15 625`, cores 0–7, 4 248.6 s —
**1.180 hours** — and it did not reach its 5 400 s backstop.

| stage | elapsed | detail |
|---|---:|---|
| basis (F4) | 20.438 s | 109 elements, 43 batches, highest pair degree 14, peak live nonzeros **28 435 493** |
| **conversion (FGLM)** | **4 226.518 s** | `D = 15 625`, 7 relations, **84 669 823** operator entries |
| univariate | 1.614 s | a point over the base field |
| **total** | **4 248.571 s** | |

> **`Anemoi(0, 34600)` has first output word zero, checked by running the permutation** —
> `is_solution`, not the polynomial system that produced it. `D = 15 625` again at run time, so the
> §5 invariant holds on the row that was actually solved rather than only on the gate.

The peak live-nonzero count is worth noting against §8a.5: **28 435 493**, well above the 20 000 000
default. The refusal that started all of this reported crossing by 112 entries, which made the
default look like a near miss; the true peak is 1.42x it. So the lift was necessary rather than
marginal, and the 112 figure was an artefact of F4 stopping the instant the budget was crossed —
exactly as `F4Error`'s own documentation says it will.

#### The cost model, which was recorded before the run

§8a.5 wrote its predictions down first, so they can be scored rather than recalled:

| quantity | predicted | measured | error |
|---|---:|---:|---:|
| conversion wall | 4 400 s (from the measured 115.2x per rung) | **4 226.5 s** | **−3.9%** |
| operator entries | ≈ 86 M | **84 669 823** | **−1.5%** |
| total wall | ≈ 1.25 h | **1.180 h** | **−5.6%** |
| dense blocks | 3.64 GiB (exact from `D`) | — | by construction |
| basis wall | ≈ 16.3 s | 20.4 s | **+25.4%** |
| peak RSS | ≈ 5.1 GiB | 4.53 GiB observed | −11% |

The conversion — the quantity the whole exercise was about — came in **within 4%** of a figure
extrapolated from measured per-rung growth, and the operator count within 1.5%. The basis estimate
was the worst of them at +25%, which is the same stage whose growth factor §8a.5 already had to
correct from 57x to 54x, and a reminder that this document's F4 extrapolations are its weakest.

**This is #286's actual deliverable.** The issue asked whether the validated `D³` model keeps
holding or breaks at the next rung. It holds: 115.2x predicted against 110.7x observed for the
conversion, against `D³`'s 125x.

#### Against the two comparands

| comparison | figure | what it is |
|---|---:|---|
| vs published Magma, conversion | **2.79x faster** | **cross-machine**, 2014 Xeon against 2022 Threadripper — not a solver comparison |
| vs published Magma, basis | **13.1x slower** | same caveat, opposite direction |
| conv/basis ratio | **206.8** against Magma's 7 548 | ratio-of-ratios **36.5x**, the machine-independent figure |
| **vs msolve, same machine** | **12.5x slower** | 4 248.6 s against 340.66 s, byte-identical generators |

So this **is** a reproduction of a published figure — 11 775.430 s of Magma conversion against
4 226.5 s here — and it is still a row this crate loses on the only comparison that holds the
machine fixed.

**One finding that qualifies §8a.7, and it moves in this crate's favour.** The msolve deficit
**narrowed** between rungs:

| rung, `PCICO` | msolve | Zeebra | deficit |
|---|---:|---:|---:|
| `N = 5` | 1.85 s | 39.0 s | **21.1x** |
| `N = 6` | 340.66 s | 4 248.6 s | **12.5x** |

Because msolve's conversion grew **184.1x** per rung and this crate's grew **110.7x**. Two rungs is
a trend and not a law, and the honest reading is narrow: **§8a.7's "one and a half orders of
magnitude" is the `N = 5` figure and should not be quoted as rung-independent.** It would be equally
wrong to project the narrowing forward — msolve's Wiedemann scalar sequence is asymptotically the
better algorithm and one crossing point proves nothing about `N = 7`. What the two rungs do support
is that the deficit is **rung-dependent**, which any competitive row quoting it must say.

#### `FCICO`, still pending

`FCICO` requested the lock at 21:43:17, immediately after `PCICO` released it, and is queued behind
the other agents' work with its 2.5 h backstop and all four F4 budgets lifted. Its attempt-1 refusal
(3.8 s, `max_matrix_rows`) stands as recorded above; whether #305 moves it is open.

> **A caution about this subsection's own instrumentation.** The monitor watching for these results
> reported `FCICO` as complete the moment `PCICO` finished — because it keyed on an `--- exit`
> marker that **attempt 1 had left in the file**, and attempt 2 had not yet started. The figures it
> reported were attempt 1's, byte-identical and entirely plausible. Caught only by comparing the
> file's mtime (20:02:16) against `PCICO`'s completion (21:43:17). This is the third instrument in
> this workstream to report confidently about the wrong object — after `pgrep -f` matching a wrapper
> on its own payload (#328) and `benchlock` logging `END status=0` for a launcher-killed run (#344)
> — and the general shape is now unmistakable: **a completion marker is not evidence of completion
> unless something ties it to the run that was supposed to produce it.**

#### What is already established at `N = 6`, independently of either run

Three results at this rung do **not** depend on a Zeebra timing landing, and they are the ones #286
was filed to get:

| established | by | value |
|---|---|---|
| `D = 15 625` = `5^6` | this crate's F4 + Hilbert series, all three characteristics | the §5 invariant, 36/36 rows |
| `D = 15 625` | the reference's own log (`unideg`, `Get rep mat`) | agreement with a printed number, not a formula |
| `D = 15 625` | msolve 0.11.0, independently | a third witness |
| conversion is reachable at this `D` | msolve, **340.66 s** on one core, 635 MB | the rung is not a wall for a modern implementation |

So the question `N = 6` was filed to answer — *is the published conversion wall real, and is this
rung reachable* — was already answered **yes, reachable** by a same-machine msolve measurement
before any Zeebra figure existed. The Zeebra figure, now in hand, adds this crate's position
against it: **1.180 h end to end with a witness verified through the permutation**, a reproduction
of the published 11 775.430 s conversion, and 12.5x behind msolve on the same machine.

### 8a.9 The binding budget, re-attributed — and it is a property of the configuration (#323)

§8a.5 closed with "the binding constraint at `N = 6` is F4, not FGLM", and #323 was filed to say so
separately. **That claim survives. Everything underneath it has moved**, because #575 changed
`F4Options::default()` on 2026-11-08 and the binding budget moved with it.

Every figure in this subsection is a **count** — no clock, nothing pinned, reproducible from
`19ff732c` plus this subsection's two subcommands:

```sh
cargo run --release --example anemoi_ladder budgets anemoi17-cico-n6
cargo run --release --example anemoi_ladder peak anemoi17-cico-n6-pcico
```

`budgets` runs the rung under four configurations **at the default budgets**, which is cheap
because a configuration that crosses one is refused early. `peak` lifts every resource budget and
reports what the row needs, which is the expensive half and the only honest input to sizing a
budget — see below for why.

#### The four configurations, and the one strategy that matters

The four vary `F4Options::default()`'s two interreduction flags, which #575 moved together. `both
off` is the default as it stood before that commit, and is the configuration every `N <= 5` figure
in §8a.3 and every figure in §8a.8 was taken under.

| row | configuration | outcome at the default budgets | peak rows | peak live nonzeros |
|---|---|---|---:|---:|
| `n5-fcico` | `default` | **refused on `max_live_nonzeros`** | 21 545 | 13 617 391+ |
| `n5-fcico` | `reduce_batch_rows: false` | completes, 109 elements | 88 166 | 1 543 889 |
| `n5-fcico` | `interreduction: Division` | **refused on `max_live_nonzeros`** | 21 545 | 13 617 391+ |
| `n5-fcico` | both off (pre-#575) | completes, 109 elements | 88 166 | 1 543 889 |
| `n6-pcico` | `default` | refused on `max_live_nonzeros`, batch 41 | 13 434 | 9 889 465+ |
| `n6-pcico` | both off (pre-#575) | refused on `max_live_nonzeros`, batch 41 | 33 599 | 13 455 206+ |
| `n6-fcico` | `default` | refused on `max_live_nonzeros`, batch 8 | 15 774 | 4 341 466+ |
| `n6-fcico` | both off (pre-#575) | **refused on `max_matrix_rows`**, batch 10 | 184 049 | 5 291 896+ |

`+` marks a peak from a refused run, which is a lower bound: F4 stops the instant the budget is
crossed, so the figure is the high-water mark of the batches that *completed*.

`interreduction` is listed because it was varied and it changes **nothing** — every arm pairs with
its `reduce_batch_rows` twin to the entry. The whole effect is `reduce_batch_rows`, and #575's own
prediction, that leaving each batch's rows reduced removes the closure the final interreduction's
matrix had to build, is what makes the second flag free here rather than merely cheap.

One small drift worth stating rather than smoothing: the pre-#575 `n6-pcico` lower bound reads
13 455 206 here against the **13 455 539** in §8a.5's quoted refusal. 333 entries in 13.5 million,
on a build six commits of F4 work later — #305 and #436 both touch symbolic preprocessing, which is
what chooses the rows. The lower bounds in this table are therefore era-sensitive in a way the
completed peaks below are not, and the completed peaks are what the conclusions use.

#### What `reduce_batch_rows` trades, measured

`peak`, with the budgets lifted, so these are what the rows actually need rather than where they
stopped:

| row | configuration | peak rows | peak columns | peak live nonzeros | over the default allowance |
|---|---|---:|---:|---:|---:|
| `n5-fcico` | `default` | 27 570 | 30 606 | **22 530 520** | **1.13x** |
| `n5-fcico` | pre-#575 | 88 166 | 91 258 | 1 543 889 | 0.08x |
| `n6-pcico` | `default` | 23 211 | 35 246 | **24 011 204** | **1.20x** |
| `n6-pcico` | pre-#575 | 82 608 | 97 388 | 28 435 493 | 1.42x |

> **`reduce_batch_rows` buys rows with entries, and the exchange rate is not constant.** At `N = 6`
> `PCICO` it is a win on both axes — 3.56x fewer rows *and* 1.18x fewer entries. At `N = 5` `FCICO`
> it is 3.20x fewer rows for **14.59x more entries**. Same flag, same family, opposite sign on the
> axis the default budget is written in.

**The pre-#575 `n6-pcico` peak reproduces §8a.8's figure exactly — 28 435 493, byte for byte** —
which is the cross-check that licenses the rest of the table. §8a.8 took it from a completed
1.180 h solve on a `f4cb0da` build; this is a basis-only run on `19ff732c` six commits of F4 work
later, and the two agree to the entry.

#### The re-attribution, in three parts

1. **The stage, within F4, has moved.** Before #575 the two models were refused on *different*
   budgets: `FCICO` on `max_matrix_rows` in **symbolic preprocessing**, `PCICO` on
   `max_live_nonzeros` in **batch elimination**. Under the default both are now refused on
   `max_live_nonzeros`, so there is one stage to aim a budget at rather than two. §8a.8's framing of
   the `FCICO` refusal as a preprocessing result is a statement about the pre-#575 configuration.
2. **It binds one rung earlier than #323 recorded.** `N = 5` `FCICO` completed on the default at
   1 543 889 live entries — 7.7% of the allowance, which is the figure `basis_options`' comment was
   written around — and is now **refused**, needing 22 530 520. Nothing in the test suite or in CI
   runs an Anemoi basis above `N = 2`, so the change was invisible. It is filed as #659.
3. **FGLM is still the second gate, and is further from binding than it was.** Nothing here touches
   the conversion: `D = 15 625` and the 3.64 GiB of dense blocks are functions of `D` alone, and
   §8a.8's 4 226.5 s conversion stands. What changed is that the first gate now refuses sooner, so
   the asymmetry §8a.5 recorded — FGLM's budgets are checked from `D` before any allocation, F4's
   are discovered by doing the work — is sharper rather than softer.

#### What a correctly aimed budget is, and why a refusal cannot size one

**A refused run reports the live count at the instant it crossed, which is the limit plus a row.**
That is `F4Error`'s documented behaviour and it makes every refusal read as a near miss:

| row | the refusal says | the peak is | the refusal understates by |
|---|---:|---:|---:|
| `n6-pcico`, pre-#575 | 20 000 112 of 20 000 000 | 28 435 493 | **1.42x** |
| `n6-pcico`, `default` | the limit plus a row | 24 011 204 | **1.20x** |
| `n5-fcico`, `default` | the limit plus a row | 22 530 520 | **1.13x** |

This is load-bearing for **#490**, which proposes lifting `max_live_nonzeros` to 25 000 000 and
lists Anemoi `N = 6` `PCICO` as one of three rows that "would then finish", on the strength of its
0.0006% overshoot. Sized against the peak instead:

- under the **pre-#575** default the row needs 28 435 493 and **25 000 000 would have been refused
  again** — the premise was wrong when it was written, for exactly the reason above;
- under **today's** default it needs 24 011 204, so 25 000 000 does clear it — by **4.1%**, on a
  quantity that moved 14.6x on another rung of the same family in a single commit.

So the correctly aimed budget for this family under the current default is **≥ 24 011 204 live
entries (385 MB at 16 bytes an entry)** for `N = 6` `PCICO` and **≥ 22 530 520 (361 MB)** for `N = 5`
`FCICO`; `N = 6` `FCICO` is not yet measured (its lifted run was not taken — see §9). #490's
25 000 000 is enough for both measured rows and is not a comfortable margin for either.

#### The Magma preprocessing comparison does not survive the configuration change

§8a.8 recorded a competitive finding: for a row Magma reduces inside a 173 808 x 189 401 matrix,
this crate's symbolic preprocessing enumerated **more than 200 000 rows** and was refused. Under
today's default the same row peaks at **15 774 rows** — 11.0x *fewer* than Magma's figure, and 7.9%
of the budget it used to cross.

That does not make this crate 11x better at preprocessing, and the reason is the caveat §8a.8
already attached: Magma's number is its peak *reduced* matrix and Zeebra's is the row set
preprocessing enumerated before reduction, so the two count different things and
`reduce_batch_rows` acts directly on the difference. **The honest statement is that §8a.8's gap was
a property of a configuration that is no longer the default, and that settling whether a gap remains
needs the counting convention settled first.** It should not be carried into #263's gap map as a
live deficit on the strength of §8a.8 alone.

#### `ACICO` at the same rung, for scale

The third model reaches the same `D = 15 625` inside every default budget (§10.3), and the margin is
not marginal:

| model at `D = 15 625` | peak live nonzeros | fraction of the 20 M allowance |
|---|---:|---:|
| `ACICO` | **879** | 0.0044% |
| `PCICO` | 24 011 204 | 120% |
| `FCICO` | > 20 000 000 | > 100% |

`ACICO`'s peak grows **linearly** in `N` — 90, 583, 693, 755, 817, 879 at `N = 1 … 6`, about +62 a
rung — against `PCICO`'s 16.3x per rung. So the rung is not the obstacle and never was the F4
obstacle: **`D = 15 625` is reachable inside the default budgets today, in the model whose
generator degrees do not compound.** What #323 attributed to F4 is attributable to F4 *for two of
the three formulations of one permutation*, which is the same lesson §10.6 draws on the clock — the
basis is a property of the model and the conversion is a property of `D`.

## 9. Open

- **`ℓ > 1` and the named hash instances.** `AnemoiSponge-BN-254` and `AnemoiSponge-BLS12-381` use
  `ℓ ∈ {1, 2}` over 255-bit fields. `Bn254Fr` and `Bls12_381Fr` exist, and `from_decimal` already
  works over them, but `smallest_primitive_root` is `u64`-only and the `ℓ > 1` linear layers are not
  implemented. Out of scope for M24-C.
- **`GF(2^n)`.** The Six Worlds results cover `n ∈ {15, …, 257}`, where `QUAD = 3` rather than 2.
  Blocked on `binary_field`/`extension_field` being exported, the same wall as the LowMC candidate.
- **`α ∈ {5, 7, 11}`.** Reference data exists for all of them in the same logs, at every prime.
  The registry records `α = 3` only. `p ∈ {65537, 2^32 − 209}` **is** now registered — see §8a.3,
  which is what #283 used them for.
- **`N = 7`.** The published basis figures say the basis step is where the cost goes above `N = 6` —
  1 623 s `FCICO` and 26 402 s `PCICO` at `p = 2^64 − 353` — so the conversion stops being the
  interesting half. §8a.9 settles that the binding constraint at `N = 6` is F4 rather than FGLM and
  that within F4 it is the live-entry budget in batch elimination, which is the ordering `N = 7`
  inherits.
- **`N = 6` `FCICO`'s peak.** §8a.9 measured the peaks for `N = 5` `FCICO` and `N = 6` `PCICO` and
  not for `N = 6` `FCICO`, whose lifted run was not taken. It is the one row in the family with no
  measured live-entry peak, so it is also the one whose budget cannot be sized from anything but an
  extrapolation — which is the mistake §8a.5 charges #286's premise with. `anemoi_ladder peak
  anemoi17-cico-n6-fcico` is the whole experiment.
- **The 64-bit `N = 6` rows.** `anemoi64-cico-n6-{fcico,pcico}` and the `2^32 − 209` pair are
  registered and gated at `D = 15 625`, but only `p = 65537` was timed, because only it has a
  published conversion to reproduce. A measurement at the other two primes would be a produced
  figure; see §8a.6 for why that is a weaker category. `PCICO` at `p = 65537` is done (§8a.8,
  1.180 h, witness verified); `FCICO` there is queued.
- **Whether the msolve deficit keeps narrowing.** It went 21.1x at `N = 5` to 12.5x at `N = 6` for
  `PCICO`, because msolve's conversion grew 184.1x per rung against this crate's 110.7x. Two rungs
  is not a trend worth extrapolating in either direction, and `N = 7` is the only thing that would
  settle it. Noted rather than claimed.
- **`ACICO`.** Done — see [§10](#10-acico-the-third-model--and-what-proved-shape-position-turns-out-to-mean).
  `ℓ > 1` and `N > 6` within that model are what remain, and §10.8 scopes them.
- **The reference's own `check_polynomial_verification` has not been executed.** It needs Sage. §4
  substitutes a stronger oracle built from committed reference output; if Sage becomes available,
  running it is still worth doing and would be a second independent check rather than the first one.

## 10. `ACICO`, the third model — and what "proved shape position" turns out to mean

**Measured at:** the wall-clock figures in §10.6 were taken at `93898118`, under
`tools/benchlock.sh`, `ZEEBRA_MACHINE=fedora ZEEBRA_AFFINITY=0-7`, `taskset --cpu-list 0-7`.
Everything else in §10 is algebraic and needs no commit to be reproducible at.

#201 (C5) asked for Campa and Roy's third model of the same primitive and for "the first proven
shape-position family". The model is here and it does what it was designed to do. The second half
did not survive reading the proof, and that is the more useful result.

**Source:** Luca Campa and Arnab Roy, *Gröbner Basis Cryptanalysis of Anemoi*, EUROCRYPT 2025,
eprint 2025/814, read in full from a local copy of the eprint PDF. Both caveats
`additional-benchmarks.md` §3.4 carried — cite the thesis, and do not quote the `d_I` columns — are
lifted there and stay lifted here.

### 10.1 The model

`ACICO` is Definition 14. At `ℓ = 1` it is `2N + 1` equations in `2N + 1` variables
`y_0, …, y_N, s_1, …, s_N`, where `s_r` is the input to the Flystel's power map at round `r` and
`y_r` is the second state word after it. The `x` half of the state is **never a variable**: it is
substituted by the Flystel verification circuit's own output, `x_r = Q_δ(y_r) + s_r^α`. That
substitution is the whole model, and it is why no degree compounds.

| generator | is | degree |
|---|---|---:|
| `a_1` | `L^{(1)}_1(0, y_0) − Q_γ(L^{(2)}_1(0, y_0)) − s_1^α` | `α` |
| `b_1` | `L^{(2)}_1(0, y_0) − y_1 − s_1` | 1 |
| `a_r`, `r > 1` | `L^{(1)}_r(m_r, y_{r−1}) − Q_γ(L^{(2)}_r(m_r, y_{r−1})) − s_r^α` | `2α` |
| `b_r`, `r > 1` | `L^{(2)}_r(m_r, y_{r−1}) − y_r − s_r` | `α` |
| `f_{N+1}` | `L^{(1)}_{N+1}(m_{N+1}, y_N)` — the output CICO condition | `α` |

Those are equations (8) and (9), and `test_the_acico_generator_degrees_are_flat_in_the_round_count`
asserts the built system against them. The contrast with `PCICO` is the point: `3, 4, 6, 8, 10, …`
there against `α, 1, 2α, α, …` here, and `ACICO`'s largest generator degree is `2α` at **every** `N`.

The variable order is the paper's ring order, `y_0 ≻ y_1 ≻ … ≻ y_N ≻ s_1 ≻ … ≻ s_N`. It is not a
free choice: Proposition 2 has `LM(g_{i,0}) = y_0`, which requires `y_0` to be the greatest of the
degree-one monomials, and a reordering changes the leading-monomial set — which
`test_the_acico_drl_basis_has_the_published_leading_monomials` catches, confirmed by running the
model with `y` and `s` swapped.

### 10.2 Faithfulness, checked against the permutation and not against the algebra

Three checks, in increasing strength, and none of them re-derives the model's own equations.

1. **Every non-output generator vanishes at a trace of the permutation**, at `N = 1 … 5`. The
   assignment comes from `Anemoi::trace`, so the model is being compared with the primitive. Only
   the output constraint may fail at an arbitrary input, and it must: a last equation that vanished
   everywhere would be a model of nothing.
2. **The output constraint *is* the permutation's first output word.** `AnemoiCico::output_word`
   evaluates `f_{N+1}` at the trace, and it equals `Anemoi(0, y).0` at every input tried. This is
   stronger than vanishing at a witness, which pins one point: it says the last equation computes
   the quantity the CICO condition is about. A sign error or a mis-ordered final linear layer
   survives the witness test and dies here.
3. **The whole system vanishes at a published witness.** `y = 1761853426583392112` at `N = 2` over
   `p = 2^64 − 353` is the root the committed Six Worlds lex basis determines (§4), so it is
   third-party data and not a point this crate chose. `ACICO` is prime-independent and the only
   published Anemoi CICO witnesses are over that field, which is why the witness check is there and
   not at the paper's prime.

No `ACICO` witness is published anywhere, so (3) borrows one from the other models — legitimate
because all three models have the same solution set. A **negative control** was run rather than
assumed: dropping `δ` from the substituted `x_r` fails checks 1–3 and leaves every structural check
in §10.3 passing, which is why the two kinds of test are separate.

### 10.3 The published structure, reproduced — Propositions 2, 3 and 4

`cargo run --release --example anemoi_acico structure`, machine-independent:

| `α` | `N` | variables | basis | Proposition 2's leading monomials | `D` | proved `(α+2)^N` | `max_pair_degree` | step degrees | peak live nonzeros |
|---:|---:|---:|---:|---|---:|---:|---:|---|---:|
| 3 | 1 | 3 | 4 | **agrees** | 5 | 5 | 4 | `[3, 4, 4]` | 90 |
| 3 | 2 | 5 | 7 | **agrees** | 25 | 25 | 6 | `[3, 4, 4, 6, 4, 4]` | 583 |
| 3 | 3 | 7 | 10 | **agrees** | 125 | 125 | 6 | `[3, 4, 4, 6, 4, 4]` | 693 |
| 3 | 4 | 9 | 13 | **agrees** | 625 | 625 | 6 | `[3, 4, 4, 6, 4, 4]` | 755 |
| 3 | 5 | 11 | 16 | **agrees** | 3 125 | 3 125 | 6 | `[3, 4, 4, 6, 4, 4]` | 817 |
| 3 | 6 | 13 | 19 | **agrees** | 15 625 | 15 625 | 6 | `[3, 4, 4, 6, 4, 4]` | 879 |

Four things in that table are worth separating.

**The leading-monomial set is Proposition 2's, exactly.** `{y_0} ∪ {y_j^α, s_j^α, y_j s_j}`, `3N + 1`
elements, at every rung. That is a far stronger reproduction than the dimension alone, because the
dimension is a *count derived from* this set and could agree while the set did not.

**The quotient dimension is `Claim::Proved`, and that is new.** §5 tags `(α + 2)^N` as
`Claim::Observed` for `FCICO` and `PCICO`, correctly: those are measurements and the designers'
statement is a conjecture. Proposition 4 **proves** the equality — "In [29] `d_I` for Anemoi is
conjectured as `d_I = (α+2)^N` for `l = 1` with experimental evidences. We prove and extend this
conjecture" — and its proof is a count of the standard monomials of Proposition 2's leading-term
ideal. So it is a statement about `⟨ACICO⟩` and about no other model of the same primitive:
`FCICO` and `PCICO` are different ideals in different rings and their agreement with `(α + 2)^N`
stays observed. `proved_acico_quotient_dimension` and `published_quotient_dimension` are two
functions with the same arithmetic and different claim strengths for exactly that reason.

**The solving degree is flat in `N`, and in a stronger form than published.** Table 6 reports
`d_solv` constant in the round count. Zeebra's F4 **step-degree sequence** is *identical* at every
`N ≥ 2` — `[3, 4, 4, 6, 4, 4]` at `N = 2, 3, 4, 5, 6` alike, not merely the same maximum.
`docs/research/degree-profiles.md` has nothing like this: round count drives degree growth on every
Poseidon family measured there. The figure quoted is `max_pair_degree`, the highest lcm degree a
batch was selected at; the published `d_solv = 9` is **not** this quantity — the paper defines it
only as "the maximum degree reached during the GB computation" with no reduction convention — so
the two numbers are not comparable and **only the flatness is**. Stated rather than silently
reported as a 6-against-9 disagreement.

**`N = 6` reaches a basis inside every default F4 budget, by four orders of magnitude.** §8a.9 is
the record of `FCICO`/`PCICO` at `N = 6` being refused on F4's live-entry budget, needing it lifted,
and taking 20 s of F4 in the one model that finished. `ACICO` reaches the same `D = 15 625` with
`F4Options::default()` untouched, at a peak of **879 live entries — 0.0044% of the 20 000 000
allowance**, against `PCICO`'s measured 24 011 204 at 120% of it. The peak column above is also
**linear in `N`**, about +62 a rung, where `PCICO`'s grows 16.3x a rung. That is a budget comparison
and so machine-independent — budgets are counts, not times.

### 10.4 `α > 3` is no longer blocked, and the published WDRL structure reproduces too

#201's question 6 answered itself in advance: "`src/poly/multivariate/monomial_order.rs` declares
exactly `{Lexicographic, GradedLexicographic, GradedReverseLexicographic}` … `ACICO` for `α > 3` is
stated over weighted-DRL and is therefore **unreachable**. Record the gap; do not improvise an
order."

**The gap closed while this issue waited.** #306 landed `MonomialOrder::Weighted` on 2026-11-08, so
WDRL is expressible with no new order and nothing improvised. `cargo run --release --example
anemoi_acico weighted`:

| `α` | `N` | basis | Proposition 3's leading monomials | `D` | proved `(α+2)^N` | `max_pair_degree` |
|---:|---:|---:|---|---:|---:|---:|
| 5 | 1 | 4 | **agrees** | 7 | 7 | 7 |
| 5 | 2 | 7 | **agrees** | 49 | 49 | 7 |
| 5 | 3 | 10 | **agrees** | 343 | 343 | 7 |
| 7 | 1 | 4 | **agrees** | 9 | 9 | 9 |
| 7 | 2 | 7 | **agrees** | 81 | 81 | 9 |
| 7 | 3 | 10 | **agrees** | 729 | 729 | 9 |
| 11 | 1 | 4 | **agrees** | 13 | 13 | 13 |
| 11 | 2 | 7 | **agrees** | 169 | 169 | 13 |
| 11 | 3 | 10 | **agrees** | 2 197 | 2 197 | 13 |

Nine rows, three exponents, Proposition 3's leading monomials `{y_0} ∪ {y_j^2, s_j^{α+1}, y_j s_j}`
on all of them, and Proposition 4's `(α + 2)^{N}` on all of them. The solving degree is flat in `N`
here too, at `α + 2`.

**The weights, and one detail the paper's prose gets backwards.** Definition 15's own example is
`w(s) = 2k`, `w(y) = αk` with ties broken by revlex, which at `k = 1` is what is used above. Those
weights satisfy the stated constraint `2w_0 ≥ αw_1` with **equality**, so `y_j^2` and `s_j^α` tie on
weighted degree and the revlex tie-break decides between them — putting `y_j^2` *above* `s_j^α`,
which is what moves the leading monomials from Proposition 2's `{y_j^α, s_j^α}` to Proposition 3's
`{y_j^2, s_j^{α+1}}`. The surrounding prose says the order is chosen "such that `y² ≺_WDRL s^α`",
which is the opposite of what Definition 15 plus those weights produces and the opposite of what
Proposition 3 needs. Recorded because an implementer following the prose rather than the definition
gets Proposition 2's structure at `α = 5`, which is precisely the case Remark 3 says DRL cannot do
efficiently.

Two things are still open at `α > 3` and neither is an order problem: no `ACICO` row is registered in
the challenge registry at any `α`, and `ℓ > 1` is blocked on the `ℓ > 1` linear layers (§9), not on
the model.

### 10.5 Shape position: a deduction, a computation, and a gap in the printed theorem

This is what #201 was for, and the answer is not the one the issue expected.

#### The theorem, as printed

Theorem 8: *let `I` be zero-dimensional and `G` a Gröbner basis of it containing, for each variable,
an element whose leading monomial is a pure power `x_i^{α_i}`; if `I` has no solutions at infinity,
then `I` has shape form in the reduced LEX basis.* Corollary 2 applies it to `⟨ACICO⟩`.

Its proof invokes Theorem 7 ([13, Theorem 1.2]), whose standing hypothesis is that **the projection
`V(I) → A¹` onto the last coordinate is injective**. Theorem 8's statement does not carry it. And
the two hypotheses Theorem 8 *does* state are one hypothesis, already implied:

- The paper's own Appendix A gives `V(I) finite ⟺ ∀i ∃f ∈ G : LM(f) = x_i^{α_i}`. The pure-power
  condition **is** zero-dimensionality.
- Under a graded order `LM(g)` is a monomial of top `deg_≺`, so `LM(top_form(g)) = LM(g)` and the
  top-form ideal's leading-term ideal contains every `LM(g)`. A pure power of each variable is
  therefore among them, the top-form quotient is finite, and the top forms cut out only the origin.
  **"No solutions at infinity" is automatic** for a Gröbner basis under a graded order.

Taken literally, Theorem 8 would say every zero-dimensional ideal is in shape form. This crate's own
corpus refutes that — `MILESTONE-FGLM-SCALABILITY.md` §8.3: cyclic's separating set is empty and 44
of 120 zero-dimensional differential fixtures fail the detector — and
`test_the_published_hypotheses_are_not_sufficient` exhibits a two-line counterexample in-crate:
planted-4 discharges every printed hypothesis, has `D = 16`, and its last coordinate has a
degree-4 minimal polynomial, because the four points of each planted pair differ only inside the
pair. The missing hypothesis is exactly what fails, and nothing syntactic about the basis can see
it.

Theorem 9 (the paper's own statement of the Shape Lemma, Appendix A) carries both missing
conditions — radicality and "the `x_n` coordinate of the points in `V(I)` are distinct" — so this
reads as an omission in Theorem 8's statement rather than a claim the paper disowns elsewhere.
Nothing here says Corollary 2's **conclusion** is false; §10.5's computations are consistent with it
at every rung tried. What is false is that the conclusion follows from the hypotheses as printed.

#### What Zeebra therefore does, in two clearly separated halves

`src/grobner/shape_certificate.rs` decides the syntactic half and names the other. It is deliberately
**not** called a certificate of shape position:

```sh
cargo run --release --example anemoi_acico shape
```

| `α` | `N` | `D` | printed hypotheses | Theorem 4-strict variables | `deg` of the lex-last variable | separating | shape basis = classical |
|---:|---:|---:|---|---|---:|---|---|
| 3 | 1 | 5 | **discharged** | `[1, 2]` | 5 | all | **yes** |
| 3 | 2 | 25 | **discharged** | `[3, 4]` | 25 | all | **yes** |
| 3 | 3 | 125 | **discharged** | `[4, 5, 6]` | 125 | all | **yes** |
| 3 | 4 | 625 | **discharged** | `[5, 6, 7, 8]` | 625 | all | **yes** |
| 5 | 1 | 7 | **discharged** | `[2]` | 7 | all | **yes** |
| 5 | 2 | 49 | **discharged** | `[3, 4]` | 49 | all | **yes** |
| 7 | 1 | 9 | **discharged** | `[2]` | 9 | all | **yes** |
| 7 | 2 | 81 | **discharged** | `[3, 4]` | 81 | all | **yes** |

- The **hypotheses** column is a *deduction* about the instance: zero-dimensionality, a pure-power
  leader per variable, and a finite `deg_≺`-top-form quotient, each computed from the basis. Cheap —
  a Hilbert series and one auxiliary F4 on the top forms.
- The **two degree columns** are a *computation* on it: `deg` of the lex-last variable's minimal
  polynomial against `D`. Equality is the separating hypothesis Theorem 8 omits. It costs a quotient
  algebra, which is `O(D²)` storage.
- The last column is the *correctness* statement, and it is asserted rather than reported: the
  reduced lex basis is unique, so a shape basis differing from the classical conversion's is simply
  wrong. `shape_lex_basis` additionally verifies its own output algebraically before returning, so
  the lex basis is certified whatever route produced it.

**The honest summary, and the three claims kept apart:**

1. **Family-level proof.** Corollary 2, cited and not reproduced here — and it inherits Theorem 8's
   omission, so it is a proof whose printed hypotheses do not support it.
2. **Instance-level deduction.** The printed hypotheses discharge on every rung above. This is
   deductive and it is *not sufficient*.
3. **Instance-level computation.** `deg = D` on every rung above, and every variable separates, not
   only the last — the same thing #224 found on `FCICO`/`PCICO`.

So **#201 does not deliver "the first proven shape-position family", and the reason is a gap in the
proof rather than a limit of this crate.** What it delivers instead is the distinction: a per-rung
machine-checked deduction of everything about shape position that is syntactic, an in-crate
counterexample showing that half is not enough, and the computation that closes it. That is strictly
more than #224's empirical 24-for-24, which has no theorem behind it at all, and strictly less than
a theorem about the family.

**The one thing the published argument does have that the syntactic check does not** is Theorem 4's
*strict* `deg_≺` condition — `f_i = c_i x_i^{α_i} + q_i` with `deg_≺(q_i) < deg_≺(LM(f_i))`, so the
top form is the bare monomial. That is genuinely stronger than "the leading monomial is a pure
power", and on `ACICO` it holds for the `s` variables and **fails** for `y_2 … y_N`, whose degree-`α`
tails carry `y_{j−1}^2 s_j`. Which is why Corollary 2 argues by back-substitution rather than by
inspection, and why `PurePower::strict` is reported per variable instead of as one boolean.

### 10.6 Where the cost goes — the basis really is free

`ACICO`, `α = 3`, `p = 1481823929`, cores 0–7, one `benchlock` acquisition:

| `N` | `D` | basis (F4) | conversion (FGLM) | univariate + roots | total | witness |
|---:|---:|---:|---:|---:|---:|---|
| 3 | 125 | 385.3 µs | 10.65 ms | 1.74 ms | 12.78 ms | none — no base-field point |
| 4 | 625 | 493.1 µs | 366.3 ms | 35.68 ms | 402.5 ms | `y = 1225307342`, **verified** |
| 5 | 3 125 | 529.1 µs | 36.13 s | 382.0 ms | 36.51 s | `y = 1452777724`, **verified** |

Both witnesses are checked by **running the permutation**, not the system that produced them.

> **The basis is free, flat, and inside the published column.** 385 µs → 493 µs → 529 µs across
> three rungs, for a quotient dimension that grows 25-fold: it is not a function of `N` in any
> useful sense, and it sits inside eprint 2025/814's own `T_GB` range of 0.0005–0.0013 s, on a
> different machine. The conversion is **98.9%** of the wall at `N = 5`.

**Five independent takings of these three rows, and the spread between them is the error bar.**
The `N = 5` conversion read 34.52 s, 34.13 s, 33.29 s, 33.10 s and 36.13 s on successive
runs — a **9.1%** spread, and the slowest came under the *lowest* reported load of the five. The
load averages were 891, 2 049, 1 874, 974 and 323, with 22, 20, 11, 9 and 27 of 6 600–9 700 threads
runnable. That the figures are insensitive to a 6.3x swing in reported load, and that the ordering
does not even correlate with it, is the clearest in-document evidence for #352's point: this box's
load average tracks tmpfs and IO pressure rather than CPU contention, and gating a measurement on it
would have blocked all five runs for nothing.

Only the last is quoted, because only it came from a binary built at the commit named above. The
earlier four were built from trees that three rebases onto a moving `main` left unreachable, which
is #505's complaint — and the reason to re-take rather than carry forward is that nobody can later
re-measure at a commit that is not in the history. The 9.1% spread is therefore also the honest
error bar on any single one of them, and no claim in §10.6 turns on a difference smaller than that:
the cross-model comparison below is four orders of magnitude.

The cross-model comparison is the finding #201 was filed for, and it holds. At the same
`D = 3 125`:

| model | basis | conversion | total |
|---|---:|---:|---:|
| `ACICO`, `p = 1481823929` | **0.00053 s** | 36.13 s | 36.51 s |
| `FCICO`, `p = 65537` (§8a.7) | ≈ 16.2 s | 47.53 s | 63.71 s |
| `PCICO`, `p = 65537` (§8a.7) | ≈ 0.8 s | 38.19 s | 39.0 s |

> **The basis is a property of the model and the conversion is a property of `D`.** `ACICO`'s basis
> is ~31 000x cheaper than `FCICO`'s and ~1 500x cheaper than `PCICO`'s at the same quotient
> dimension, while the three conversions sit within 1.3x of each other. One primitive, one `D`,
> three formulations, and the entire spread is in the half the model controls.

Two caveats, both binding. The `ACICO` rows are at the 31-bit prime the paper measures over and the
`FCICO`/`PCICO` rows at 17 bits, so the comparison is cross-characteristic; §8a.3's finding that this
crate's cost is characteristic-flat to 12% across a 47-bit range is what makes it defensible, and it
is an inference rather than a measurement. And the ambient load average read 323 during the run
with only 27 of 6 638 threads runnable — this box's load is tmpfs and IO pressure rather than CPU
contention (#352), so the figures are not contended, but they are not from a quiet machine either.

**Root finding is not yet the wall, and the published data says where it becomes one.** It is 1.1%
of the total at `N = 5` here. eprint 2025/814's Table 7 puts the crossover at `α = 3, N = 8`:
14 567 s of factoring against 1 213 s of Wiedemann. Here the share is **falling** rather than
rising — 13.6%, 8.9%, 1.0% of the total at `N = 3, 4, 5` — because this crate's conversion grows
faster per rung than its root finding does at these sizes. So the crossover, if it arrives, arrives
later here than in the reference, and nothing at `N ≤ 5` is evidence about where.

So #201's question 5 — "`ACICO` may be the first cryptanalytic family whose bottleneck is the
univariate layer" — is **not yet true at the rungs reachable here**, and the published figures locate
where it would become true. `N = 6` would cost ≈ 1.2 h of conversion by §8a.8's measured per-rung
growth and was not run.

### 10.7 What `ACICO` says about the sparse-FGLM no-go, and about `shape.rs` as a strategy

**On `MILESTONE-FGLM-SCALABILITY.md` §8.5.** `ACICO` is evidence about that no-go from the opposite
direction to #214's, and it **strengthens** it. #214's argument was that the conversion is where the
cost is, so an alternative conversion is where the win would be. `ACICO` makes that sharper rather
than weaker: with the basis at 0.00053 s the conversion is 98.9% of the wall, so the family is
*entirely* a conversion benchmark. But [`order-conversion.md`](order-conversion.md) §5.B already
settles which alternative, on this family's own published data — SparseFGLM wins at `d_I = 5^4`,
loses by 9.1x at `5^6` and **fails** at `5^8` where Wiedemann returns in 1 212.9 s. So the no-go
stands for the reason #224 gave: a sparse-FGLM milestone would build the route that gives out first,
and the faster of the two is already scoped as #368. Nothing in §10 widens #368's scope; it adds the
family where its target is 98.9% of the cost instead of 82.8% (§8a.4).

**On promoting `fglm::shape` to an `FglmOptions` strategy (question 7).** The recommendation is
unchanged from `order-conversion.md` §5.A: **do not**, and `ACICO`'s positive result does not change
it. The reason is §8.3's measurement, not detection: the Krylov shape route is 0.37x on the route at
`D = 64` because it replaces the frontier's sparse-early vectors with a variable's powers, which
densify immediately. Shape position being *available* on a family says nothing about the route being
*cheaper* on it. What `ACICO` does add is the strongest reason yet to wire the **detector** into the
planner (#273), because the planner now has two cryptanalytic families where it fires and a cheap
syntactic pre-filter — `shape_position_hypotheses` costs a Hilbert series — that can be read before
paying for a quotient algebra. Routed to #273 and #224; not duplicated here.

**On "verify the inputs are already a Gröbner basis" (#201 gap 4, shared with #202).** `ACICO`'s
input generators are **not** a Gröbner basis — the DRL basis has `3N + 1` elements against `2N + 1`
generators, and the extra `N` are the degree-two filter equations `y_j s_j` that Proposition 2's
quotient count depends on. So the capability #201 asked for would answer "no" on this family, and
the thing actually worth having here is the weaker and more useful one Zeebra now has:
**check the basis against a predicted leading-monomial set**, which is what
`test_the_acico_drl_basis_has_the_published_leading_monomials` does and what caught the variable
ordering in the negative control. #202's FreeLunch case is different — there the inputs genuinely
are claimed to be a basis — so the proposal belongs with #202 and not here, with this note attached:
`ACICO` is not a second consumer for it.

### 10.8 Open, in `ACICO`

- **No `ACICO` row is registered.** The model variant exists and
  `ChallengeParameters::AnemoiCico`'s digest admits it (#201 gap 5 is satisfied: a third `model`
  line, no collision), but no row was added, so `anemoi_ladder` cannot reach `ACICO` and
  `examples/anemoi_acico.rs` is the runner. Registering rows means new digests and a frozen-registry
  edit, which is its own change against a registry several agents touch —
  [#643](https://github.com/mfaulk/zeebra/issues/643), which also records that
  `PublishedWithoutAnswer` is the right `ExternalStatus` here because the paper publishes timings
  and `d_I` but no witness.
- **`N ≥ 6` timings.** The `N = 6` *basis* is free and inside every default budget (§10.3); the
  conversion at `D = 15 625` projects to ≈ 1.2 h and was not run. `N = 7, 8` is where the published
  data says factoring overtakes everything, and `N = 8` means `D = 390 625`, far past this crate's
  conversion reach.
- **`ℓ > 1`.** `ACICO`'s stated advantage over `FCICO`/`PCICO` is that it "extends past two
  branches", and that is the half of the model this issue did not implement: `Anemoi::new` refuses
  `ℓ ≠ 1` and the `ℓ > 1` linear layers are §9's standing gap. Proposition 4's `(α + 2)^{Nℓ}` is
  therefore untested for `ℓ > 1`, and so is Table 6's second flatness claim — `d_solv` constant
  across `ℓ = 1, 2, 3` as well as across rounds. [#644](https://github.com/mfaulk/zeebra/issues/644).
- **The `d_solv` definition.** Zeebra reports `max_pair_degree`; the paper reports an undefined
  "maximum degree reached". Only the flatness is compared (§10.3). Matching the number would need
  the paper's convention, which is not stated.
- **Theorem 8's omission has not been reported upstream.** §10.5 is this repository's reading of the
  printed text, checked against the paper's own Theorem 9 and against an in-crate counterexample.
  Telling the authors is an owner action rather than an agent one —
  [#645](https://github.com/mfaulk/zeebra/issues/645).
