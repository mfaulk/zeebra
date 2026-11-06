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

The **count** is checked too, not only the values: the log's own `nsols` line reports 2, 1, 0 and 1
solutions at `N = 1, 2, 3, 4`, and the root-finding agrees at every rung including the empty one.
`N = 3` contributes no witness because the reference found none either.

**A trap worth recording.** The variable labels in the Six Worlds logs are *positionally permuted*
relative to the model's own names. `models.sage` re-interprets each specialized polynomial into a
fresh ring whose variable list is the fast ordering, and the names bind by position, so the generator
the log prints as `X0100` is the model's `Y0000` — the CICO input. The two orders coincide at `N = 1`
and diverge from `N = 2` on, which is exactly the shape of bug that passes the easiest case. Reading
the logs by label without accounting for this yields points that satisfy no equation.

## 5. The machine-independent invariant, as the reference reports it

`dim F_p[x]/I` does not depend on the machine, the library or the wall clock. The committed logs
report, for `α = 3` and both models:

| `N` | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| quotient dimension | 5 | 25 | 125 | 625 | 3125 |

which is `(α + 2)^N` exactly. This is tagged `Claim::Observed` and **not** `Claim::Proved`: it is a
measurement from one implementation, and the designers' corresponding statement is a conjecture.

A disagreement between this and Zeebra's own `D` is a **defect in Zeebra or in the model, not a
performance difference**, and it stops the workstream rather than becoming a table entry.

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

## 8. Open

- **`ℓ > 1` and the named hash instances.** `AnemoiSponge-BN-254` and `AnemoiSponge-BLS12-381` use
  `ℓ ∈ {1, 2}` over 255-bit fields. `Bn254Fr` and `Bls12_381Fr` exist, and `from_decimal` already
  works over them, but `smallest_primitive_root` is `u64`-only and the `ℓ > 1` linear layers are not
  implemented. Out of scope for M24-C.
- **`GF(2^n)`.** The Six Worlds results cover `n ∈ {15, …, 257}`, where `QUAD = 3` rather than 2.
  Blocked on `binary_field`/`extension_field` being exported, the same wall as the LowMC candidate.
- **`α ∈ {5, 7, 11}` and `p ∈ {65537, 2^32 − 209}`.** Reference data exists for all of them in the
  same logs. The registry records `α = 3` at `p = 2^64 − 353` only, because that is the row where
  the published FGLM cost is 2 400× the F4 that preceded it.
- **`ACICO`.** A third model of the same primitive (`additional-benchmarks.md` §3.4). Cheap once the
  permutation exists, and a separate issue.
- **The reference's own `check_polynomial_verification` has not been executed.** It needs Sage. §4
  substitutes a stronger oracle built from committed reference output; if Sage becomes available,
  running it is still worth doing and would be a second independent check rather than the first one.
