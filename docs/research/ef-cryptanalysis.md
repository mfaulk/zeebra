# EF cryptanalysis programmes: parameters, objectives, and what is already solved

Reference for #71 (A2), under the cryptographic-corpus epic #67. Consumes the provenance
conventions of `docs/research/external-provenance-policy.md` §9 and the four-claim ledger of
`docs/research/minrank.md`. `docs/research/poseidon.md` is the implementation record for the one
family this repository has already ported; this document is the survey behind it.

**No measurement.** Nothing here is a timing, a benchmark or an estimate produced by this crate.
§7 records two pieces of ground truth established by running *other people's* verifiers, which is
what #71 asks for; everything else is read from a published source.

---

## 0. Sources of record

Read in place, with the bytes pinned. All accessed **2026-11-07**.

### Primary — the programmes themselves

| short name | what it is | URL | sha256 | bytes |
|---|---|---|---|---|
| **`initiative`** | Poseidon Cryptanalysis Initiative 2024–2026: running team, all four 2026 families with their current status, the 2025 programme, the Gröbner grant, the changelog | <https://www.poseidon-initiative.info/> | `bfc77af16503e821d855d32b913c70a9891c1ac05db34541257d98b71d392516` | 289 612 |
| **`spec2026`** | *Bounty challenges for Poseidon Initiative 2026* — the LaTeX source of the PDF `initiative` links. Formal problem statements, attack analyses, instance parameters | [`raw.githubusercontent.com/khovratovich/poseidon-tools/main/bounties/docs/bounty2026.tex`](https://raw.githubusercontent.com/khovratovich/poseidon-tools/main/bounties/docs/bounty2026.tex) | `f9186fcd4cbb440e83a2ff39379ad74600daad1fdbabd53833a137f70c2aba65` | 7 505 |
| **`tools`** | `khovratovich/poseidon-tools` at `60075da7c0521d9493749a035b1f30d4eda37138` (2026-05-14), Apache-2.0 — the verifiers and sample challengers `initiative` names | <https://github.com/khovratovich/poseidon-tools> | README `f81118936eb6e9c33a314019fc8df46e6b907004f6bc6983ba07b38e1874ec87` | — |
| **`hm2026`** | the "details here" page for the **2025** programme: per-instance round numbers and the organizers' own interpolation-versus-Gröbner complexity table | <https://hackmd.io/gW6ccot5QfSRXvgXqoL8GA?both> | `—` (see §11) | 4 416 |
| **`bounties21`** | EF ZK Hash Function Cryptanalysis Bounties 2021, the site itself | <https://www.zkhashbounties.info/> | `f2343072863c29ec08ea214be845163be4463f2e23941cfa457f951498976152` | 140 450 |
| **`hm2021`** | *Algebraic Hash Function Bounties* — the "Decomposition and alpha/beta values" page `bounties21` links. **The complete parameter tables, with a `Real Attack Cost` column**: the only published results for that programme | <https://hackmd.io/l2JT8AQITJ2xRZpGErPnzA> | `8f5c1bd66a38afbcf1aa21a61e80e452a732174dbc67ea3249a654c8d04f46d2` | 5 345 |
| **`zoo`** | `krypto/zkfriendlyhashzoo` at `b9c09d5a6302725a65ff59e4219d1beb4c524154`, MIT — the "Reference implementation and bounty instances" `bounties21` links, cloned with full history | <https://extgit.iaik.tugraz.at/krypto/zkfriendlyhashzoo> | per file in §4 | — |
| **`mimc`** | *MiMC Hash Challenge Bounty*, EF + Protocol Labs | <https://crypto.ethereum.org/bounties/mimc-hash-challenge> | `c3e5aa80e8c51cc7d081b8f2dc9f1391f26ef5daf567ffff7a56f55294e1654e` | 50 002 |

### Wayback, used to date a change rather than to read a document

| snapshot | why |
|---|---|
| [`web/20211101211629`](https://web.archive.org/web/20211101211629id_/https://www.zkhashbounties.info/) | "Parameters are fixed on **November 1st** 2021"; **no** broken-parameter note |
| [`web/20211207075233`](https://web.archive.org/web/20211207075233id_/https://www.zkhashbounties.info/) | "Parameters are fixed on **November 23d** 2021"; the Feistel-MiMC note has appeared |
| [`web/20231201191020`](https://web.archive.org/web/20231201191020id_/https://www.zkhashbounties.info/) | identical to the live page apart from the reference-implementation links |

**Licensing.** `tools` is Apache-2.0; `zoo` is MIT (Graz University of Technology, 2021). Both
permit reuse with attribution. Nothing is vendored here regardless: this document records
parameters and results, and §8 names what a future corpus entry should generate rather than copy.
`initiative`, `bounties21` and `mimc` are web pages read as publications.

---

## The finding, before the detail

Three results, in descending order of how much they should change what this repository does.

1. **The organizers have published a request for exactly zeebra's pipeline, and it is unclaimed.**
   `initiative`'s *Gröbner Basis Exploratory* asks for a DRL Gröbner basis by F4 or F5 on
   reduced-round Poseidon, a basis conversion to LEX, a univariate factorization to recover the
   preimage, **with the cost of each step counted separately in CPU operations and memory**, so
   that a formula for the full instance can be extrapolated. That is `f4` → `fglm_to_lex` →
   `solve_one` with `peak_memory`, which is what this crate already is. Both bounty programmes
   additionally say a Gröbner attack "may qualify for an additional bonus" where they expect an
   interpolation or resultant attack to win. §3.5.

2. **The three 2026 CICO instances are all solved, and the programme is closed.** `R_P = 6` on
   2026-04-10, `R_P = 8` on 2026-05-06, `R_P = 10` on 2026-07-06, each with a verified solution.
   So `docs/research/poseidon.md`'s target family is a **reproduction** target, not an open one —
   which is a better thing to be, because a result there can be checked against someone else's.
   §3.3.

3. **Every field every one of these programmes uses is already implemented here.** #71 states that
   KoalaBear "is not currently implemented"; it is, as `fields::KoalaBear`. So is M31, Goldilocks,
   the 2021 bounties' `2^64 − 59`, and both BN254 and BLS12-381 `Fr`. The field gap #71 expected to
   find does not exist. §6.

And one that is a caution rather than an opportunity: **the four published artifacts of the 2026
programme disagree with each other on two parameters**, and in one case the disagreement would
send a solver after a different hash function. §3.4.

---

## 1. The M20-E boundary, decided

#71 names this blocking, so it is settled first.

`docs/MILESTONE-LARGE-PRIME-FIELDS.md` describes **M20-E** in four words — "Crypto corpus, oracle,
measurements" — and its status line says the milestone's only remaining item is "M20-E's benchmark
corpus". That is a work item about *this repository's* machinery. #71 is a question about *the
outside world*.

**Decision, as #71 proposes and this document adopts:**

| | owns |
|---|---|
| **M20-E** | the in-crate corpus: generators, the oracle, fixtures, registry entries, and any measurement |
| **#71 (this document)** | the survey: which programmes exist, which parameters are authoritative and where they are published, what objective each poses, what has already been solved and by whom, and which candidates are worth M20-E's effort |

The split is clean because the two have no shared artifact: this document adds no field, no
generator, no fixture and no row to `src/grobner/research/challenge.rs`'s registry. §8 is a
prioritized shortlist, which is an input to M20-E and not a part of it.

---

## 2. The objectives, and why substituting one for another invalidates everything

#71 insists every candidate carry exactly one objective type. These are the ones that occur, with
the discriminating question for each.

| objective | what is fixed | polynomial-system target? |
|---|---|---|
| **CICO(`k`)** | `k` input words and `k` output words of the **permutation**; solve for the remaining `t − k` | **yes** — this is the one |
| **Preimage** through a hash mode | the capacity is fixed by the construction, and the digest is prescribed | yes, but the mode decides the system |
| **Partial collision** | nothing; find `x ≠ y` agreeing on the first `t` outputs | **no** — birthday-bounded, `O(p^{t/2})` generically |
| **Density** | a zero pattern in the input must be reproduced by decoded hash outputs | **no** — a fixed-point/search condition, not a root-finding one |
| **Zero-test** | a degree-`≤ d` polynomial must vanish at a hash of its own coefficients | **no** — self-referential; the unknown is the polynomial |
| **Full-state permutation inversion** | everything | **not a problem at all** — a permutation is invertible |

Two refinements that the pages' own phrasing obscures, both established from verifier code in §3
and §4.

- **`k = 1` versus `k = 2` is not a matter of how many words the page prints.** `bounties21` states
  its task as `Perm(X1,X2,0) = (Y1,Y2,0)`, which reads as two constrained outputs. The verifier
  checks `output[t-1] == 0` and nothing else: `Y1, Y2` are names for whatever comes out. It is
  **CICO(1)**. §4.1.
- **The 2025 and 2026 CICO instances are different problems** even at the same `t` and `k`. 2025
  fixes zeros at the *end* of input and output; 2026 fixes prescribed constants at the *start* and
  zeros at the start of the output, and inserts a linear layer before the first round. §3.2, §3.3.

---

## 3. Programme A: the Poseidon Cryptanalysis Initiative

`initiative`, run by the EF Poseidon Group — George Kadianakis, Dmitry Khovratovich, Antonio Sanso
— with an advisory board of Aumasson, Ben-Sasson, Hopwood, Lubarov and Rothblum. Phase 2 concludes
December 2026 and focuses on **Poseidon1 over KoalaBear**. `initiative` discloses that Khovratovich
is a Poseidon designer and that the Poseidon team helped define the bounty parameters.

Three separate prize programmes run concurrently, and they are easy to conflate.

### 3.1 The Poseidon1 Collision Prize — paused, one tier claimed

| | |
|---|---|
| objective | **partial collision** (§2) — not a solving target |
| instance | Poseidon-31: Poseidon1, KoalaBear `p = 2^31 − 2^24 + 1 = 2130706433`, `d = 3`, `t = 16`, `R_F = 8`, `R_P = 20`, compression mode, 16-element output |
| task | find 15-element `X ≠ Y` with `H(0xc09de4, X) = H(0xc09de4, Y)` on the first `q` elements |
| MDS | "arbitrary but satisfying no-invariant-subspace-trail conditions"; `initiative` names the Plonky3 circulant matrix as an example |
| status | **PAUSED from 1 Aug 2026 AoE**; the prize program itself runs to 2029-01-01 |
| budget | $992 000 |
| tiers | `q = 3` **$32K, claimed 6 April 2026**; `q = 4` $64K; `q = 5` $128K; `q = 6` $256K; `q = 7` $512K |

**The `0xc09de4` prefix is load-bearing and the reference README gets it wrong.** `initiative`
states `H(0xc09de4, X)`, and `tools`' `partial_collision_verifier._hash` computes
`([SEED] + inputs)[:t_perm]` with `SEED = 0xc09de4`. The README instead documents
`H(inputs) = compression_mode_hash([0] + inputs)`. A solver built from the README would search a
different function and every solution it found would be rejected. §3.4.

`spec2026`'s own analysis gives the generic bound as `m(m-1)/(2 p^t)` for `m` hash calls. Its
source carries a **per-tier expected-complexity table inside a `\begin{comment}` block**, so it is
absent from the compiled PDF: `t = 2`: `2^31.5`, `t = 3`: `2^47`, `t = 4`: `2^62.5`, `t = 5`:
`2^78`, `t = 6`: `2^93.5`, `t = 7`: `2^109`. Recorded as read-from-source-and-deliberately-
unpublished, not as a published figure.

The claimed `q = 3` solution is in the repository and verifies; §7.

### 3.2 Bounty Program 2025 — preimage/CICO over three Poseidon families

Ran to 2025-12-01, budget $130 000. Objective: **CICO**, phrased as "find a preimage of 0".

| family | source | field | `d` | `t` | task |
|---|---|---|---:|---:|---|
| Poseidon-256 | Poseidon1 | **BLS12-381 `Fr`** | 5 | 3 | `Perm(X1,X2,0) = (Y1,Y2,0)` — CICO(1) |
| Poseidon-64 | Poseidon2 | **Goldilocks** `2^64 − 2^32 + 1` | 7 | 8 | `Perm(X1..X7,0) = (Y1..Y7,0)` — CICO(1) |
| Poseidon-31 | Poseidon2 | **M31** `2^31 − 1` | 5 | 16 | `Perm(X1..X14,0,0) = (Y1..Y14,0,0)` — CICO(2) |
| Poseidon-31 | Poseidon2 | **KoalaBear** | 3 | 16 | as above — CICO(2) |

Round numbers and claims, from `initiative` and `hm2026` (which agree):

| instance | `R_F` | `R_P` | stated level | bounty | claimed |
|---|---:|---:|---|---|---|
| Poseidon-256 | 6 | 8 | 24-bit | $4 000 | **9 Dec 2024** |
| Poseidon-256 | 6 | 9 | 28-bit | $6 000 | **31 Dec 2024** |
| Poseidon-256 | 6 | 11 | 32-bit | $10 000 | — |
| Poseidon-256 | 6 | 16 | 40-bit | $15 000 | — |
| Poseidon-64 | 6 | 7 | 24-bit | $4 000 | **23 Apr 2025** |
| Poseidon-64 | 6 | 8 | 28-bit | $6 000 | **27 Apr 2025** |
| Poseidon-64 | 6 | 10 | 32-bit | $10 000 | **24 May 2025** |
| Poseidon-64 | 6 | 13 | 40-bit | $15 000 | — |
| Poseidon-31 M31 | 4 | 0 | 24-bit | $4 000 | 29 Nov 2025 (§11) |
| Poseidon-31 KoalaBear | 4 | 1 | 24-bit | $4 000 | 30 Nov 2024 (§11) |
| Poseidon-31 M31 | 4 | 1 | 28-bit | $6 000 | 29 Nov 2024 (§11) |
| Poseidon-31 KoalaBear | 4 | 3 | 28-bit | $6 000 | 29 Nov 2024 (§11) |
| Poseidon-31 M31 | 6 | 1 | 32-bit | $10 000 | 2 Dec 2025 (§11) |
| Poseidon-31 KoalaBear | 6 | 4 | 32-bit | $10 000 | 5 Dec 2024 (§11) |
| Poseidon-31 M31 | 6 | 4 | 40-bit | $15 000 | 5 Nov 2025 |

**"24-bit estimated security" is a label, not a measured cost.** `hm2026` explains the
construction: for Poseidon-256 and Poseidon-64 the organizers fed `κ` into the designers' own
round-number script with `R_F = 6`; for Poseidon-31 that produced unbreakable round counts, so they
instead set `R_F = 4` and chose `R_P` to make the interpolation attack cost slightly more than the
same-level Poseidon-256 and Poseidon-64 instances. The levels are therefore **not comparable across
families**.

`hm2026` also publishes the organizers' own `log2` cost estimates for both attack routes, which is
the single most useful table in the programme for this repository because it is a prediction a
Gröbner implementation can be measured against:

| level | Poseidon-256 interp / GB | Poseidon-64 interp / GB | Poseidon-31 KB interp / GB | Poseidon-31 M31 interp / GB |
|---|---|---|---|---|
| 24-bit | 31 / **63** | 34 / **89** | 37 / **32** | 37 / **37** |
| 28-bit | 36 / **70** | 37 / **92** | 41 / **44** | 40 / **46** |
| 32-bit | 38 / **73** | 43 / **100** | 45 / **63** | 45 / **65** |
| 40-bit | 50 / **91** | 51 / **111** | — | 52 / **87** |
| 128-bit | 149 / **245** | 134 / **159** | — | 133 / **147** |

Note the sign flip: Gröbner is *cheaper* than interpolation only for Poseidon-31 KoalaBear at the
24-bit level (32 against 37), and roughly level with M31 at 24-bit (37 against 37). Everywhere else
the organizers expect Gröbner to lose, by between 10 and 60 bits. **Poseidon-31 KoalaBear,
`R_F = 4`, `R_P = 1` is the one instance in the whole 2025 programme where the organizers' own
estimate makes a Gröbner attack the better route**, and it is an already-claimed tier, so a result
there is checkable. §8.

### 3.3 Bounty Program 2026 — four families, two finished, one paused

Runs to 2027-01-01, budget $150 000. All over Poseidon-31: Poseidon1, KoalaBear, `d = 3`, `t = 16`.
Verifiers and sample solvers at `tools`.

#### CICO — **FINISHED**, all three instances solved

| | |
|---|---|
| objective | **CICO(2)** — `initiative` calls it "a partial preimage of 0", "a 62-bit preimage" |
| task | find `X1..X14` with `Perm⁺(0xc09de4, 0xee6282, X1..X14) = (0, 0, Y1..Y14)` |
| `Perm⁺` | "the inner sponge permutation of Poseidon1 **with an extra linear layer before the first round**" (`initiative`); `tools` exposes it as `permutation_plus_linear` |
| parameters | `k = 2`, `t = 16`, `R_F = 6`, **`R_P ∈ {6, 8, 10}`**, `C_1 = 0xc09de4`, `C_2 = 0xee6282`, `C_3 = C_4 = 0` |
| generic rate | `1/p^k ≈ 2^-62` (`spec2026`; checked, `2 log2 p = 61.98`) |

| instance | bounty | status |
|---|---|---|
| `R_F = 6`, `R_P = 6` | $6 000 | **solution verified 10 April 2026** |
| `R_F = 6`, `R_P = 8` | $10 000 | **solution verified 6 May 2026** |
| `R_F = 6`, `R_P = 10` | $15 000 | **solution verified 6 July 2026** |

> "We expect that the best attack that solves these bounties is a **resultant attack**. A Groebner
> basis attack that breaks any of these instances may qualify for an additional bonus."

That sentence is the programme's own assessment, and it is why
`docs/research/resultant-elimination.md` and `docs/research/hybrid-cico-cost.md` exist. **No
solution is published** — only the verification
dates — so the solutions themselves are not available as witnesses (§11).

#### Zero-test — **FINISHED**, six tiers claimed

| | |
|---|---|
| objective | **zero-test** (§2) — not a solving target in the CICO sense |
| task | find `P` of degree `7` over `F_{p^2}` such that the first two hash output elements, read as an `F_{p^2}` element, is a root of `P` |
| parameters | `r = 2`, `d = 7`, `ell = 8`, `s = 1`, `R_F = 6`, **`R_P > 5`**; `F_{p^2} = F_p[x]/(x^2 − 3)` |
| generic rate | `d/p^r ≈ 2^-59.2` (`spec2026`; checked, `2 log2 p − log2 7 = 59.17`) |
| fund | $40 000, ranked by the `R_P` broken; **solutions kept confidential except the `R_P`** |

Records, with `initiative`'s own wording preserved because it distinguishes two states:

| `R_P` | status as stated |
|---:|---|
| 7 | "Claimed and **verified** June 3d, 2026" |
| 8 | "Claimed and **verified** June 6th, 2026" |
| 9 | "Claimed and **verified** June 29th, 2026" |
| 10 | "**Claimed** July 7th, 2026" |
| 11 | "**Claimed** July 22nd, 2026" |
| 12 | "**Claimed** July 27th, 2026 (two simultaneous submissions)" |

`R_P = 10, 11, 12` are recorded as claimed and **not** stated as verified. That distinction is the
page's and is preserved rather than smoothed.

#### Density — **PAUSED**

| | |
|---|---|
| objective | **density** (§2) — not a solving target |
| task | find `S` with two zero entries at attacker-chosen `i1, i2` such that every output element of `H(S)`, raised to `(p−1)/16`, is `ω^{i1}` or `ω^{i2}`, where `ω = 148625052` is a 16th root of unity in `F_p` |
| parameters | `k = 1`, `d = 2`, `r = 16`, `ell = 16`, `t = 16`, `R_F = 6`, **`R_P > 5`** |
| generic rate | `(d/r)^16 = 2^-48` (`spec2026`; checked exactly) |
| fund | $40 000, ranked by `R_P`; solutions confidential except the `R_P` |

`ω = 148625052` matches `tools`' `density_verifier._OMEGA` exactly.

#### Partial collision in the 2026 programme

`spec2026` and `tools` carry a fourth family — Poseidon1 compression mode, `ell = 16`, `R_F = 8`,
`R_P = 20`, challenge target `t = ell` — which is the §3.1 prize restated. Treated as one family,
not two.

**A fifth family exists only as commented-out source.** `spec2026` contains a complete
*multi-target collision* challenge, with instance parameters `k = 2^16`, `ell = 2`, and a `2^-62`
rate, entirely inside `\begin{comment}`. It was drafted and not published.

### 3.4 Where the four published artifacts disagree

Four artifacts describe the 2026 programme: `initiative` (the web page), `spec2026` (the formal
spec), the `tools` README, and the `tools` verifier code. They do not agree, and the disagreements
are worth knowing before writing a solver.

| # | subject | `initiative` | `spec2026` | README | verifier code | verdict |
|---|---|---|---|---|---|---|
| 1 | CICO `R_P` | `{6, 8, 10}` | `{6, 8, 10}` | **`{8, 10, 12}`** | `{6, 8, 10}` | **the README is wrong**, three-to-one |
| 2 | collision prefix | `H(0xc09de4, X)` | — | **`[0] + inputs`** | `[0xc09de4] + inputs` | **the README is wrong**, and it changes the function |
| 3 | CICO's extra linear layer | **stated** | *silent* | stated | `permutation_plus_linear` | the spec is incomplete; the verifier is operative |
| 4 | density / zero-test `R_P` | `> 5` | `> 5` | `6` | `6`, commented "must be > 5 per spec" | not a conflict: `6` is the least admissible value, and the challenge is a **family** |

Defect 1 matters because `R_P = 12` is not an instance of this programme at all, and `R_P = 6` —
the easiest and the first solved — is missing from the README's set. Defect 2 matters more: it is
the difference between two distinct hash functions.

A fifth, smaller one: `cico_verifier.py`'s own comment reads
`CICO_RP = 8  # bounty offers R_P ∈ {6, 8, 10}; default = 8 (hardest)`. Eight is not the hardest of
`{6, 8, 10}` — ten is, since more partial rounds is strictly harder. An agent picking "the hardest"
from that default picks the middle instance.

Defect 4 deserves emphasis rather than correction: because `R_P > 5` is open-ended, the density and
zero-test challenges have **no hardest instance**, which is exactly why the funds are ranked by the
`R_P` broken rather than paid per tier. A fixture that pinned `R_P = 6` for these would be pinning
the implementation's default, not the challenge.

### 3.5 The Gröbner Basis Exploratory — the programme that describes this crate

Quoted at length because it is a specification of work this repository is already most of the way
through:

> Existing Groebner basis research papers on Poseidon have very imprecise complexity estimates. We
> would like to launch a more detailed investigation of attack complexity so that the complexity of
> a full attack can be extrapolated from the ones on small instances. … Construct a DRL-order
> Groebner basis using F4 or F5 GB algorithms for reduced-round versions of Poseidon-256, -64, -31,
> as specified in the Bounty Program, for all feasible combinations of `RF` and `RP`. … Run the
> basis conversion algorithm in order to get the LEX basis … Solve the preimage problem by
> factoring a univariate polynomial from the LEX basis. **The complexity of these steps should be
> counted separately, both in terms of memory requirements and CPU operations.** From the table of
> practical complexities, a formula for the full instance should be extrapolated.

Mapping onto what exists here: DRL is grevlex, which is `grobner::f4`'s working order; the basis
conversion is `fglm_to_lex`; the univariate factorization is `poly::univariate::factorize` and
`solve_one`; per-step memory accounting is `util::peak_memory` plus `F4Options::max_live_bytes` and
`FglmOptions::max_span_bytes`. The requested deliverable — a table of per-step practical
complexities across feasible `(R_F, R_P)`, from which a formula is extrapolated — is the shape of
the M23/M24 scoreboard work.

Two notes on eligibility and timing, recorded rather than acted on: applications were due
2025-04-01 (and the 2026 short-term grants by 2026-06-01), and `initiative` states that Poseidon
authors may not apply. **Nothing here is a grant application**; the relevance is that the
organizers have written down which numbers they want and in what units, which makes them a
specification for a measurement rather than a competitor's claim.

`initiative`'s 2026 short-term-grant list also names *Attack with resultants* explicitly, citing
resultants' recent use against Anemoi, Jarvis and Rescue-Prime — which is
`docs/research/resultant-elimination.md`'s and `docs/research/anemoi.md`'s territory.

---

## 4. Programme B: the EF ZK Hash Cryptanalysis Bounties, 2021–2022

`bounties21`, with the complete parameter tables on `hm2021` and the instances in `zoo`. Deadline
2022-11-30; technical reports public by 2022-12-01; `bounties21` states a total budget of $200 000
while `hm2021` states 30 ETH (§11). Field for all of Rescue-Prime, Poseidon and Feistel-MiMC:

> `p = 18446744073709551557 ≈ 2^64`

which is `2^64 − 59`, the largest 64-bit prime, and is `fields::Zp18446744073709551557` here.

### 4.1 The objective is CICO(1), as the verifier defines it

`bounties21` states the task as `Perm(X1,X2,0) = (Y1,Y2,0)`. `zoo`'s verifier for each instance is
an example program; the operative check is, verbatim:

```rust
let input = [solution1, solution2, Scalar::zero()];
let output = poseidon.permutation(&input);
if output[output.len() - 1] == Scalar::zero() { println!("Challenge solved!"); }
```

One input word fixed to zero, one output word checked against zero: **CICO(1)**. For the `t = 2`
Rescue-Prime instances and for Feistel-MiMC the shape is `Perm(X,0) = (Y,0)`, also CICO(1).

The whole programme is therefore a single objective type, and it is the one type this crate
targets.

### 4.2 Rescue-Prime — and `m` is not always 3

`zoo`'s `bounties/src/rescue_prime/rescue_prime_instances.rs`
(`5d8474b90f735a3fa2a2f8311e8a6867d7c4203d07ca8d502807d65f469facc9`), where
`RescuePrimeParams::new(t, d, rounds, mds, round_constants)`:

| instance | `t` (= `m`) | `α` | rounds `N` | stated level | est. cost | bounty | **published real cost** |
|---|---:|---:|---:|---:|---|---|---|
| `EASY1` | **3** | 3 | 4 | 25 | `2^39` | $2 000 | **`2^43`, 4 days** |
| `EASY2` | **2** | 3 | 6 | 25 | `2^41` | $4 000 | est. `2^53` |
| `MEDIUM` | **2** | 3 | 7 | 29 | `2^49` | $6 000 | est. `2^62` |
| `HARD1` | **3** | 3 | 5 | 30 | `2^51` | $12 000 | est. `2^57` |
| `HARD2` | **2** | 3 | 8 | 33 | `2^56` | $26 000 | est. `2^72` |

Parameters from `zoo`; the level, estimate, bounty and real-cost columns from `hm2021`. **The two
sources agree on every `(t, N)` pair**, which is the check worth having since they are an
implementation and a prose table.

**#71 records Rescue-Prime as `m = 3`; three of the five instances are `m = 2`.** The MDS and
round-constant tables in `zoo` corroborate the widths independently: `MDS2` is `2×2` and `MDS3` is
`3×3`, and each round-constant block has `2N` rows of width `t` — 8×3 for `N = 4`, 12×2 for
`N = 6`, 14×2 for `N = 7`, 10×3 for `N = 5`, 16×2 for `N = 8`. Every one matches.

`hm2021` also states how the two cost columns were produced: the estimate substitutes `α, N, m`
into the Gröbner complexity estimate of the Rescue-Prime spec §2.5, and the "security level"
substitutes `α, 2N/3, m` into the same estimate. So **both columns are the designers' own formula,
not measurements** — except the single `2^43` (4 days) entry, which is a real executed attack.

### 4.3 Poseidon 2021 — three executed attacks with wall-clock times

`zoo`'s `poseidon_instances.rs`
(`2d277ce93e260b8771cbe158b484911183df00533b64d32ccb91068b61407e9d`), where `PoseidonParams::new(t,
d, rounds_f, rounds_p, mds, rc)`. All `t = 3`, `d = α = 3`,
`R_F = 8`:

| `R_P` | stated level | est. cost | bounty | **published real cost** |
|---:|---:|---|---|---|
| 3 | 8 | `2^40` | $2 000 | **`2^26`, 1 second** |
| 8 | 16 | `2^49` | $4 000 | **`2^35`, 13 minutes** |
| 13 | 24 | `2^58` | $6 000 | **`2^44`, 36 hours** |
| 19 | 32 | `2^69` | $12 000 | est. `2^54` |
| 24 | 40 | `2^77` | $26 000 | est. `2^62` |

`R_P ∈ {3, 8, 13, 19, 24}` in `zoo` matches `hm2021` exactly. These three wall-clock figures are
the most directly comparable published results in the whole survey: a CICO(1) problem, `t = 3`,
over a 64-bit prime this crate implements, at round counts a workstation can reach. **No hardware
is stated** for any of them, which is why they are a difficulty ladder rather than a comparand
(§11).

Note the direction of the error: every real cost is **13 to 14 bits below** the designers' own
estimate, consistently across the three executed instances. That is a property of the published
record worth carrying forward.

### 4.4 Feistel-MiMC — the broken parameter set, recovered exactly

`bounties21` says only: "The initial parameters were broken and were replaced." #71 asks which set
is authoritative. Both sets are now established, from two independent directions.

**The authoritative (replacement) set**, `zoo`'s `feistel_mimc_instances.rs`
(`bb093e58d08a508659c163944fb83e4f47c5112e5c9f44962df07b6ff5eddd38`), where
`FeistelMimcParams::new(d, rounds)`, `α = d = 3`:

| rounds `r` | stated level | est. cost | bounty | published real cost |
|---:|---:|---|---|---|
| 22 | 18 | `2^36` | $2 000 | est. `2^47` |
| 25 | 20 | `2^40` | $4 000 | est. `2^52` |
| 30 | 24 | `2^48` | $6 000 | est. `2^60` |
| 35 | 28 | `2^56` | $12 000 | — |
| 40 | 32 | `2^64` | $26 000 | — |

**The broken set.** `hm2021` keeps two rows labelled `OLD`, and they are the two that were solved:

| rounds `r` | stated level | est. cost | bounty | **published real cost** |
|---:|---:|---|---|---|
| **14** | 12 | `2^24` | $6 000 | **`2^33`, 3 minutes** |
| **18** | 15 | `2^32` | $12 000 | **`2^40`, 6 hours** |

`hm2021` lists only the solved two. `zoo`'s git history gives the **whole** original ladder: commit
`e69d08f612f8534ef60651cb01fc326b67230ec1`, 2021-12-20, "update the feistel-mimc instances",
replaces `r ∈ {6, 10, 14, 18, 22}` with `r ∈ {22, 25, 30, 35, 40}`.

So the ladder shifted up wholesale, and **the old hardest instance (`r = 22`) became the new
easiest**. Two sources, two halves of one answer: `hm2021` says which old instances fell and at
what cost, `zoo`'s history says what the old ladder was.

One inconsistency, recorded: `bounties21` says "Parameters are fixed on November 23d 2021" (and the
2021-11-01 snapshot said November 1st), but the replacement commit is dated **2021-12-20**, four
weeks after the stated fixing date.

`hm2021` adds two useful notes: full 64-bit security needs **81 rounds** (`64 · log_3 4`), and "we
are not aware of anything better than equation solving which costs about `3^r` for `r` rounds" —
i.e. the designers' own expectation for this family *is* an algebraic attack.

### 4.5 Reinforced Concrete — rejected, and the reason is structural

Parameters agree across `hm2021` and `zoo`'s `reinforced_concrete_instances.rs`
(`92a81fda288ee1fab74f140c7988dd96abd7011bd1901ac74ae172dea368db44`), where
`ReinforcedConcreteParams::new(d, si, v, ab)`, all with `d = t = 3`:

| instance | prime | `log2 p` | `v` | `(α1, α2, β1, β2)` | level | est. cost | bounty |
|---|---|---:|---:|---|---:|---|---|
| `EASY` | `281474976710597` | 48 | 223 | `(1, 2, 3, 4)` | 24 | `2^48` | $4 000 |
| `MEDIUM` | `72057594037926839` | 56 | 617 | `(1, 3, 2, 4)` | 28 | `2^56` | $6 000 |
| `HARD` | `18446744073709551557` | 64 | 541 | `(1, 3, 2, 4)` | 32 | `2^64` | $12 000 |

Every value matches between the prose page and the Rust source, including the `v` and the
`(α, β)` tuples — a complete cross-check.

**#71 asks whether Reinforced Concrete is expressible as a polynomial system at all. It is not, at
any useful degree.** Its S-box decomposes a field element into digits in mixed radices
`s_1 … s_6` (or `s_7`) and applies `f(x) = (x == 0) ? 0 : x^{-1} mod v` per digit — a table lookup
over a *different* modulus `v`. Digit decomposition is not a low-degree polynomial map over `F_p`,
and the per-digit inversion is modulo `v`, not `p`. The programme agrees from the other side:
`bounties21` says "The best attack we have found for these variants is exhaustive search" and
"Groebner basis challenges **might** be declared additionally" — they never were, and no real
attack cost is published for any of the three. **Rejected**, and not for want of effort.

---

## 5. Programme C: the MiMCSponge collision challenge — rejected as a solving target

`mimc`, run jointly by the Ethereum Foundation and Protocol Labs. MiMCSponge is a sponge
instantiated with the MiMC-Feistel permutation over a prime field.

| parameter | BN254 | BLS12-381 |
|---|---|---|
| field prime | `21888242871839275222246405745257275088548364400416034343698204186575808495617` | `52435875175126190479447740508185965837690552500527637822603658699938581184513` |
| rounds | 220 | 220 |
| exponent | **5** | **5** |
| `r` | 1 | 1 |
| `c` | 1 | 1 |

Both primes match this crate's `fields::Bn254Fr` and `fields::Bls12_381Fr` moduli exactly, and
`src/fields/prime_field_256.rs` already checks its limbs against the published decimals with
`ark-ff` as an independent oracle.

**Objective: collision**, at 128-bit and 80-bit target security — so **not a polynomial-solving
target**, exactly as #71 anticipates. A collision is birthday-bounded and a Gröbner basis has
nothing to contribute to it. Its value here is as a specification and an arithmetic exercise over
the M20 fields: 220 rounds of `x^5` over a 254-bit field is a real exercise of
`PrimeFieldElement256` and of the wide `pow_mod_limbs` path M20-D added.

Reference code is `circomlib`'s MiMCSponge, with the constants generated by a linked script; the
page also points at the MiMCSponge circuit, the MiMC-Feistel EVM bytecode and the Solidity
implementation, and offers rewards for significant bugs in those.

**Two things about this page are not recoverable, and one of them is a duplicated row.** Its reward
table has exactly two body rows and they are **identical** — both read "Collisions on the proposed
220 rounds, on either of the fields, targeting 128-bit security | $20,000" — while the page's own
introduction promises rewards for "128-bit **and 80-bit** security". So the 80-bit challenge's
statement and its reward are stated nowhere on the page. Verified against the raw HTML, not just a
rendering. §11.

---

## 6. The fields: all of them already exist here

#71's task 3 asks which programmes need a field this crate does not have. **The answer is none**,
and #71's own premise — "KoalaBear … is a 31-bit prime and is not currently implemented" — is
stale.

| programme | field | prime | in this crate |
|---|---|---|---|
| Initiative 2026, all four families | KoalaBear | `2^31 − 2^24 + 1 = 2130706433` | **`fields::KoalaBear`** = `PrimeFieldElement32<2130706433>` |
| Initiative 2025, Poseidon-31 | M31 | `2^31 − 1 = 2147483647` | **`fields::Mersenne31`**, also `Zp2147483647` |
| Initiative 2025, Poseidon-64 | Goldilocks | `2^64 − 2^32 + 1 = 18446744069414584321` | **`fields::Zp18446744069414584321`** |
| Initiative 2025, Poseidon-256 | BLS12-381 `Fr` | 255-bit | **`fields::Bls12_381Fr`** |
| Bounties 2021, all three algebraic families | — | `2^64 − 59 = 18446744073709551557` | **`fields::Zp18446744073709551557`** |
| MiMCSponge | BN254 `Fr`, BLS12-381 `Fr` | 254-, 255-bit | **`fields::Bn254Fr`**, **`fields::Bls12_381Fr`** |
| Bounties 2021, Reinforced Concrete | — | `281474976710597`, `72057594037926839` | **not declared**, but `PrimeFieldElement64<P>` instantiates at either; moot, since §4.5 rejects the family |

The zero-test family additionally needs `F_{p^2} = F_p[x]/(x^2 − 3)` over KoalaBear.
`src/fields/extension_field.rs` provides degree-2 extensions, so this is a declaration rather than
new arithmetic — but the family is a zero-test, not a solving target (§2), so it is not on the
shortlist.

The relationship to #62 is therefore the reverse of what #71 assumes: the 32-bit prime field
landed, KoalaBear is one of its instantiations, and no field work blocks any candidate here.

---

## 7. Ground truth, established without this crate

#71 asks for a `poseidon-tools` verifier to be run on a published solution, or failing that on a
solution from its own sample solver, *before* any zeebra code is written. Both were done. Neither
is a measurement of this crate and no timing is recorded.

**1. The published `q = 3` partial collision verifies.** `tools` ships
`bounties/submissions/partial_collisions.py`
(sha256 `bb68de7942773ff70778228624bc1bf6e0973f91e89fdbc4a68415239c0ec694`), attributed in its own
docstring to **Izan Beltran, Simon-Philipp Merz, Àlex Rodríguez García and
Matteo Scarlata**. Running it at `tools`' HEAD:

```
X        = [146101246, 585745660, 1080651781, 0, …, 0]
Y        = [310195439, 1632272689, 97247552,  0, …, 0]
H(X)[:3] = [776343852, 1993637744, 983127350]
H(Y)[:3] = [776343852, 1993637744, 983127350]
verify_collision_solution(t=3) -> True
```

Three leading output words agree and the official verifier accepts. This is the `q = 3` tier
`initiative` records as **claimed on 6 April 2026** — so the record, the claim date and the witness
line up across three sources.

One note on the file: it computes `padded_X = [SEED] + X` and never uses them. Vestigial, and
consistent with the author checking the same `0xc09de4` prefix that §3.4 defect 2 is about.

**2. The relaxed CICO variant produces a checkable solution.** `cico_sample_challenger` with
`m = 5, seed = 42` found free inputs in **5 241 attempts** against an expected `2^{m·k} = 2^10`,
and the three verifiers agree as they should:

| check | result |
|---|---|
| `verify_cico_solution_relaxed(m=5)` | **True** |
| `verify_cico_solution_relaxed(m=6)` | False |
| `verify_cico_solution` (exact) | False |

So the relaxed ladder is a genuine ladder — a solution at `m` is not one at `m + 1` — and
reproducible by seed. That is the right first target for an implementation, because correctness can
be checked against someone else's verifier before difficulty is attempted.

---

## 8. Prioritized shortlist

Ordered by what a result would be worth divided by what it would cost. Every entry is **CICO**;
§2's other objectives are excluded on principle, not on difficulty.

| # | candidate | field | objective | why | why not |
|---|---|---|---|---|---|
| **1** | 2026 CICO relaxed, `R_F = 6`, `R_P = 6`, `m` small | KoalaBear | CICO(2) | an official verifier accepts or rejects it, the ladder is reproducible by seed (§7), and `m` tunes the difficulty continuously from trivial upward. The only candidate where correctness is checkable before difficulty is attempted | not a record; a relaxed variant is not the bounty |
| **2** | 2026 CICO exact, `R_F = 6`, `R_P = 6` | KoalaBear | CICO(2) | **already solved and verified, 2026-04-10**, so a result reproduces a known one; `poseidon.md` has the port and the test vectors; `$6 000` tier | the organizers expect a resultant attack to win (§3.3); `hybrid-cico-cost.md` closes two routes already |
| **3** | 2025 Poseidon-31 KoalaBear, `R_F = 4`, `R_P = 1` | KoalaBear | CICO(2) | **the one instance where the organizers' own estimate makes Gröbner the cheaper route** — 32 bits against interpolation's 37 (§3.2) — and the tier is claimed, so checkable | `R_P = 1` is a very reduced instance; the claim is an interpolation attack, so there is no Gröbner figure to match |
| **4** | 2021 Poseidon, `t = 3`, `R_F = 8`, `R_P ∈ {3, 8, 13}` | `2^64 − 59` | CICO(1) | **three published executed attacks with wall-clock times** (1 s, 13 min, 36 hr) — the only such ladder in the survey — on a `t = 3` system over a field this crate has | no hardware published (§11), so a difficulty ladder and not a comparand; `t = 3` is far from the deployed `t = 16` |
| **5** | 2021 Feistel-MiMC, `r ∈ {14, 18}` (the **OLD** set) | `2^64 − 59` | CICO(1) | two published executed attacks (3 min, 6 hr) at `2^33`/`2^40`; the simplest construction in the survey — a Feistel with `x^3` and no MDS | the parameters are retired, so a result is a reproduction of a break of a withdrawn instance |
| **6** | 2021 Rescue-Prime, `t = 3`, `N = 4` | `2^64 − 59` | CICO(1) | one published executed attack, `2^43` in 4 days; `hm2021` states the exact formula both its cost columns come from, so four numbers are checkable | the `2^43` is the costliest executed result in the 2021 programme |
| **7** | 2025 Poseidon-256, `R_F = 6`, `R_P = 8` | BLS12-381 `Fr` | CICO(1) | `t = 3`, `d = 5`, over a field M20-B implemented and M20-C already runs F4/FGLM/`solve_one` over; claimed 2024-12-09 | the organizers put Gröbner 32 bits behind interpolation here (63 against 31) |

Not on the list, and deliberately: the 2026 CICO `R_P = 8` and `R_P = 10` instances, which are
harder versions of entry 2 and should wait on it; and every `R_P > 5` density or zero-test
instance, which have no hardest member (§3.3) and are not solving targets.

---

## 9. Rejected, with reasons

| candidate | objective | reason |
|---|---|---|
| Poseidon1 Collision Prize (all tiers) | partial collision | birthday-bounded. `spec2026`'s own bound is `m(m-1)/(2p^t)`; the `q = 3` tier cost `~2^47` hash calls. A Gröbner basis contributes nothing to a collision search |
| 2026 Density (all `R_P`) | density | a search for an input whose hash decodes onto its own zero positions. Not a root-finding problem, and `R_P > 5` means there is no hardest instance to aim at |
| 2026 Zero-test (all `R_P`) | zero-test | self-referential: the unknown is a polynomial whose coefficients are hashed to produce the point it must vanish at. Not expressible as a fixed polynomial system |
| 2026 multi-target collision | collision | **never published** — exists only inside a `\begin{comment}` block in `spec2026` |
| Reinforced Concrete (all three) | CICO(1) | **not expressible as a polynomial system** at any useful degree: mixed-radix digit decomposition plus a lookup `x^{-1} mod v` with `v ≠ p`. The programme itself says exhaustive search is its best attack and never declared the Gröbner variant it floated (§4.5) |
| MiMCSponge, both curves | collision | collision at 128-bit target security (§5). Worth implementing as a specification over the M20 fields; not solvable |
| Full-state permutation inversion of anything here | — | trivial; a permutation is invertible. Named only because it is the mistake #71 warns about |
| 2025 Poseidon-64, any tier | CICO(1) | Goldilocks exists here, but the organizers put Gröbner **55 to 68 bits** behind interpolation on this family (89 vs 34 at 24-bit) — the worst ratio in their table |

---

## 10. Corrections to the record

1. **KoalaBear is implemented.** #71 says it "is not currently implemented"; it is
   `fields::KoalaBear`. So are M31, Goldilocks, `2^64 − 59`, BN254 `Fr` and BLS12-381 `Fr`. No
   candidate in this survey is blocked on a field. (§6)
2. **The 2026 CICO `R_P` set is `{6, 8, 10}`.** `initiative`, `spec2026` and the verifier code all
   say so; only the `poseidon-tools` README says `{8, 10, 12}`. `docs/research/poseidon.md` §1
   already had it right. (§3.4)
3. **The partial-collision hash prefixes `0xc09de4`, not `0`.** The README's
   `compression_mode_hash([0] + inputs)` contradicts `initiative` and the verifier, and it defines
   a different function. (§3.1, §3.4)
4. **The 2026 CICO permutation has an extra linear layer before the first round**, which
   `spec2026` does not mention at all. The verifier's `permutation_plus_linear` is operative.
   (§3.3, §3.4)
5. **Rescue-Prime's bounty instances are not all `m = 3`.** Three of the five are `m = 2`. #71
   records `m = 3`. (§4.2)
6. **The 2021 bounty objective is CICO(1), not CICO(2).** The page's `Perm(X1,X2,0) = (Y1,Y2,0)`
   reads as two constrained outputs; the verifier checks one. (§4.1)
7. **Feistel-MiMC's broken set was `r ∈ {6, 10, 14, 18, 22}`** and the authoritative replacement is
   `r ∈ {22, 25, 30, 35, 40}`. The old hardest became the new easiest. (§4.4)
8. **The 2025 and 2026 CICO instances are different problems** — different constrained positions,
   and only the 2026 one has the extra linear layer. (§2, §3.2, §3.3)
9. **Density and zero-test are `R_P > 5`, open-ended.** The implementation's `R_P = 6` is the least
   admissible value, not the challenge. These two challenges have no hardest instance by
   construction. (§3.3)
10. **Poseidon-31 in the 2025 programme is two instances, not one** — M31 with `d = 5` and
    KoalaBear with `d = 3`, at different `R_P` for the same stated level. (§3.2)
11. **Reinforced Concrete should be rejected on expressibility**, which #71 asks to be assessed
    before scoping. It is not a polynomial system at any useful degree. (§4.5)
12. **`initiative`'s own changelog records a corrected prime**: "29 Nov 2024 — a typo in the Koala
    Bear prime definition was fixed (`2^32` → `2^31`)". Anything quoting that page before that date
    may carry the wrong field.

---

## 11. Secondary-only, uncertain, and not established

**Nothing in §1–§9 rests on secondary literature.** Every parameter, objective, status, date and
cost was read from a programme's own page, its own linked detail page, its own specification
source, or its own reference implementation. Where two of those disagree, §3.4 and §10 say which
won and why.

**Not established.**

- **The 80-bit MiMCSponge challenge.** `mimc`'s reward table has two identical 128-bit rows while
  its prose promises 128-bit *and* 80-bit. The 80-bit statement and reward appear nowhere on the
  page. (§5)
- **Hardware for any 2021 result.** `hm2021` publishes wall-clock times (1 s, 13 min, 36 hr,
  3 min, 6 hr, 4 days) and no machine, for any of them. So those are a difficulty ladder and cannot
  be a comparand for a timed run here. (§4.3, §4.4)
- **The 2026 CICO and zero-test solutions themselves.** Only verification dates are published for
  CICO, and the zero-test and density funds state explicitly that submissions are "kept
  confidential (except for the `RP` value)". So there is **no witness** for any 2026 CICO or
  zero-test record — unlike the partial collision, whose `q = 3` witness is in the repository
  (§7). An importer cannot be checked against them.
- **Which Poseidon-31 claim date belongs to which 2025 tier.** `initiative` writes, for instance,
  "24-bit: RF=4, RP=0 (M31) claimed 29 Nov 2025 and RP=1 (KoalaBear). $4000 claimed 30 Nov 2024",
  mixing a 2025 and a 2024 date in one line with one bounty figure. The table in §3.2 reproduces
  the dates as printed and does not assign them. The changelog's "29 Nov 2024 — 24-bit bounty
  claimed for Poseidon-31" suggests the 2025 dates may be typos for 2024, but that is an inference
  and is not asserted.
- **Whether the three 2026 zero-test tiers marked "Claimed" (`R_P = 10, 11, 12`) were verified.**
  The page says "claimed and verified" for `R_P = 7, 8, 9` and only "claimed" for the rest. The
  distinction is preserved; its meaning is not established. (§3.3)
- **The 2021 programme's total budget.** `bounties21` says "$200 000"; `hm2021` says "30 ETH". The
  per-instance bounties in `hm2021` sum to about $190 000 including the two OLD rows, which is
  consistent with the dollar figure; the ETH figure is not reconciled.
- **The 2021 parameter-fixing date.** `bounties21` ended at "November 23d 2021" (it said
  "November 1st" on 2021-11-01, and `hm2021` still says November 1st), but the Feistel-MiMC
  replacement commit is dated 2021-12-20. The stated date precedes the change it describes.
- **Whether any 2021 bounty was formally awarded**, and to whom. `hm2021`'s `Real Attack Cost`
  column establishes that attacks were executed; no page names a winner, and the technical reports
  the terms require ("released to the public domain at latest December 1st 2022") were not located.
- **Whether `tools`' README defects are known upstream.** Not reported; no issue was filed on
  another project's repository under this issue.

**Attempted and failed, with what was tried.**

| target | what was tried | result |
|---|---|---|
| the per-primitive round tables on `bounties21` | the live page (they are four signed `lh7-us.googleusercontent.com/sitesv-images-rt/…` images, not HTML tables, so there is no text to extract); refetched with a browser `User-Agent` and a `Referer`; then searched three Wayback captures for archived copies | **`403` on every image URL, and Wayback archived none of the four.** The round numbers are **not recoverable from the page**. Obtained instead from `hm2021` and from `zoo`, which agree with each other — so the loss costs nothing, but a reader who only has the page cannot get the parameters |
| *Survey of attacks on Poseidon and Poseidon2*, the follow-up `initiative` links | `https://eprint.iacr.org/2024/886.pdf` | **`403`**, the same host-wide PDF block recorded in `minrank.md` §9, `fukuoka-mq.md` §13 and `elimination-beyond-grobner.md` §8. Not pursued further: the survey is needed for the *Attack Reward Program*'s "improvement over the survey" criterion, which no candidate in §8 relies on |
| a `sha256` for `hm2026` | `https://hackmd.io/gW6ccot5QfSRXvgXqoL8GA/download` | **served, and quoted, but not pinned.** HackMD's rendered HTML carries session-varying markup and its Markdown export is not content-addressed, so a digest over either would not be reproducible. The two tables taken from it are reproduced in §3.2 in full instead, which is the auditable substitute. `hm2021` exported stably and *is* pinned |
| the GitLab REST API for `zoo` | `extgit.iaik.tugraz.at/api/v4/projects/krypto%2Fzkfriendlyhashzoo/repository/tree`, and `…/projects?search=` | `404` and a non-JSON `200`. Irrelevant in the end — `git clone` over HTTPS works, and `git fetch --unshallow` gave the history §4.4 depends on |
| a published 2021 technical report | — | **not located.** The terms require them public by 2022-12-01; neither `bounties21` nor `hm2021` links any, and no winner is named |
