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
| The Six Worlds experimental output (MIT, commit `fa056e6f`) | `models.sage`, `anemoi.sage`, `attack.sage` and `results/anemoi_p18446744073709551263_n1_l1_a3_m{F,P}CICO_o1.txt` via `raw.githubusercontent.com/IAIK/six-worlds-anemoi` |

Both reference repositories are MIT, so their data *may* be redistributed — which the Fukuoka files
cannot be, see [`fukuoka-mq.md`](fukuoka-mq.md) §3. Nothing is copied here that is not cited: the
only committed reference numbers are the four CICO witnesses in `src/grobner/research/anemoi.rs`
and the per-step figures in the registry's `ReferencePoint` rows, each traceable to the `results/`
file named above.

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

### 8a.1 The comparison that survives the hardware gap

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
there. This is the first externally calibrated evidence about `fglm`'s scaling, and it is favourable
— which is why it needs the careful framing rather than less of it.

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

## 9. Open

- **`ℓ > 1` and the named hash instances.** `AnemoiSponge-BN-254` and `AnemoiSponge-BLS12-381` use
  `ℓ ∈ {1, 2}` over 255-bit fields. `Bn254Fr` and `Bls12_381Fr` exist, and `from_decimal` already
  works over them, but `smallest_primitive_root` is `u64`-only and the `ℓ > 1` linear layers are not
  implemented. Out of scope for M24-C.
- **`GF(2^n)`.** The Six Worlds results cover `n ∈ {15, …, 257}`, where `QUAD = 3` rather than 2.
  Blocked on `binary_field`/`extension_field` being exported, the same wall as the LowMC candidate.
- **`α ∈ {5, 7, 11}` and `p ∈ {65537, 2^32 − 209}`.** Reference data exists for all of them in the
  same logs. The registry records `α = 3` at `p = 2^64 − 353` only, because that is the row where
  the published FGLM cost is 2 400× the F4 that preceded it.
- **`N = 6`, where the reference has no conversion figure at all.** The Six Worlds logs report a
  basis at `N = 6` (132.5 s `FCICO`, 372.2 s `PCICO`) and a dash for the conversion — they stop
  reporting it after `N = 5`. Zeebra converts at `D = 3 125` in 46 s, and the validated `D³` model
  puts `D = 15 625` at roughly 1.6 h. So `N = 6` is reachable here and would produce a figure the
  reference does not have, which is a different kind of contribution from reproducing one. It needs
  a deliberate registry addition — the ladder is frozen at `N = 1 … 5` — and a memory estimate
  first: operator entries go 12.6 M at `D = 3 125`, and 25x that is not obviously affordable. Filed
  rather than attempted.
- **`ACICO`.** A third model of the same primitive (`additional-benchmarks.md` §3.4). Cheap once the
  permutation exists, and a separate issue.
- **The reference's own `check_polynomial_verification` has not been executed.** It needs Sage. §4
  substitutes a stronger oracle built from committed reference output; if Sage becomes available,
  running it is still worth doing and would be a second independent check rather than the first one.
