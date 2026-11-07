# Anemoi: what was taken unchanged, what was verified, and what is a reconstruction dependency

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

This is also the measurement that settles §8.5's sparse-FGLM no-go for this family rather than
overturning it. Sparse FGLM attacks the operator construction; here the operator construction is
16.7% and falling. Nothing in §8.5's three measurements is contradicted.

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
| `n6-pcico` | **340.66 s** (re-taken) | 635 MB | §8a.8 | §8a.8 | 11 777.0 s |

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

All figures in this subsection are on **`origin/main` including #305**, which is a different build
from §8a.3's `N ≤ 5` column (commit `eb79e05`, pre-#305). #305 bounds symbolic preprocessing's
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

*Outcome pending; this subsection is completed with whatever it produces, including a backstop.*

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
rung reachable* — is already answered **yes, reachable**, by a same-machine measurement, before any
Zeebra figure. What a Zeebra figure adds is this crate's position against it, which §8a.7 has
already established is one and a half orders of magnitude behind.

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
  interesting half. And #323 records that the binding constraint at `N = 6` was already F4 rather
  than FGLM, which is the ordering `N = 7` inherits.
- **The 64-bit `N = 6` rows.** `anemoi64-cico-n6-{fcico,pcico}` and the `2^32 − 209` pair are
  registered and gated at `D = 15 625`, but only the `p = 65537` rows were timed, because only they
  have a published conversion to reproduce. A measurement at the other two primes would be a
  produced figure; see §8a.6 for why that is a weaker category and §8a.8 for what was run.
- **`ACICO`.** A third model of the same primitive (`additional-benchmarks.md` §3.4). Cheap once the
  permutation exists, and a separate issue.
- **The reference's own `check_polynomial_verification` has not been executed.** It needs Sage. §4
  substitutes a stronger oracle built from committed reference output; if Sage becomes available,
  running it is still worth doing and would be a second independent check rather than the first one.
