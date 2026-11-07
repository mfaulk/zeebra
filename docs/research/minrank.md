# Courtois MinRank challenges A–F: the parameters, and the instances that never existed

Reference for F1 (#205), under the MinRank epic #195. Consumes the provenance conventions of
`docs/research/external-provenance-policy.md` §9 and the redistribution discipline of
`docs/research/fukuoka-mq.md` §3.

**Sources of record.** Three primary documents, each read in place rather than through a search
summary, with the bytes pinned:

| short name | what it is | how it was obtained | sha256 | accessed |
|---|---|---|---|---|
| **`asia01`** | Courtois, *Efficient Zero-knowledge Authentication Based on a Linear Algebra Problem MinRank*, Asiacrypt 2001, LNCS 2248 pp. 402–421; IACR ePrint 2001/058 | `eprint.iacr.org` PDFs 403 here, so the Wayback Machine's capture of the author's own ePrint PDF: [`web.archive.org/web/20040723070613id_/http://eprint.iacr.org/2001/058.pdf`](https://web.archive.org/web/20040723070613id_/http://eprint.iacr.org/2001/058.pdf) | `bbdfe4521eb102eb7dc137bea245f2a6ec186ee9fddf2b5b906a2cbfc0daee34` (256 966 B, 19 pp.) | 2026-11-07 |
| **`FauSafSpa10`** | Faugère, Safey El Din, Spaenlehauer, *Computing Loci of Rank Defects of Linear Matrices using Gröbner Bases and Applications to Cryptology*, ISSAC 2010 | author mirror, [`members.loria.fr/PJSpaenlehauer/data/papers/FauSafSpa10a.pdf`](https://members.loria.fr/PJSpaenlehauer/data/papers/FauSafSpa10a.pdf) | `eeb0330b0490c6296c5b33d2515b84b072358ca7a883e141b548bff0fda201ad` (146 591 B, 8 pp.) | 2026-11-07 |
| **`MinRank2.0`** | Aragon, Bros, Perlner, Smith-Tone, Verbel, *Cryptanalysis of MinRank 2.0*, IACR ePrint 2026/2733 | **abstract page only**; the PDF still 403s and Wayback has no capture (§9) | — | 2026-11-07 |

Licensing, per `external-provenance-policy.md` §4: `MinRank2.0` is **CC BY** (stated on its ePrint
page). The artifact repository in §5.3 is **GPL-3.0** and its data is therefore *not* redistributed
here. `asia01` and `FauSafSpa10` are read as publications; nothing is copied from either.

---

## 1. The finding, before the detail

The epic's premise was that the challenge *matrices* might not survive. The stronger and better
supported conclusion is that **there never were any**. §4.3 of `asia01` says, in the author's own
words:

> We propose six sets of parameters A-F that use square matrices (η = n) and work either over
> GF (2) or over GF (65521), the biggest prime that fits in 16 bits.

Six **sets of parameters**. The paper publishes a table of `(q, η, n, m, r)` with attack costs,
a construction for generating instances, and no instances. It offers no prize, no data file, no
download URL. The scheme's own official page — `http://www.minrank.org/minrank/`, named in the
paper's header — is archived eight times between 2001 and 2003 and carries papers and slides only
(§3.2).

So the honest classification for all six is the same, and it is not "lost":

> **A–F are authentic, primary-sourced parameter sets. No authentic instance exists for any of
> them, and none appears ever to have been published.**

That is a cleaner position than "the data is lost", because it means a same-parameter instance is
not a degraded substitute for something better — it is **the same kind of object every published
result on these challenges used** (§5). The published cost figures remain a difficulty scale rather
than a comparand, for the ordinary reason that MinRank instances are random.

---

## 2. The parameter table, read from the original source

### 2.1 The problem

`asia01` §3, verbatim in substance:

> Let `M₀; M₁, …, M_m` be some `η × n` matrices over a ring `R`. The problem `MinRank(η, n, m, r, R)`
> is to find a solution `α ∈ R^m` such that `Rank(Σᵢ αᵢ Mᵢ − M₀) ≤ r`.

Two things follow that the epic's framing had wrong, and they are not cosmetic.

1. **The formulation is inhomogeneous.** The public data is `1 + m` matrices, not `m`. #205's
   motivation describes the verifier as "form `Σ αᵢ Mᵢ` and call `rank`"; the actual condition
   subtracts `M₀`. For challenge A that is **eleven** `6 × 6` matrices, not ten. A verifier that
   omitted `M₀` would reject every correct witness.
2. **`R = GF(q)` for the challenges** — §3.1, "In our scheme `R` will be a finite field `GF(q)`" —
   and the `q` row prints `65521`, a prime, not `2^16`. Research question 6 of #205 is answered:
   **`Z/65521`, not `GF(2^16)`.** 65521 is the largest prime below `2^16`.

The self-verification claim survives intact: given `α`, the check is one rank computation over the
declared field. It is the cheapest witness check of any family in the corpus.

### 2.2 The table

`asia01` §4.3, page 7. Transcribed from the rendered page image as well as from `pdftotext`,
because every attack cost in the table is a superscript and text extraction flattens them.

| | A | B | C | D | E | F | *HFE Chall. 1* | *Quartz* |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `m` (unknowns) | 10 | 10 | 10 | 81 | 121 | 190 | *80* | *103* |
| `n` | 6 | 7 | 11 | 19 | 21 | 29 | *80* | *103* |
| `η` | 6 | 7 | 11 | 19 | 21 | 29 | *80* | *103* |
| `r` | 3 | 4 | 8 | 10 | 10 | 15 | *7* | *8* |
| `q` | 65521 | 65521 | 65521 | 2 | 2 | 2 | *2^80* | *2^103* |
| `Pr_α[Rank ≤ r]` | 0.6 | 0.6 | 0.6 | 0.6 | 0.6 | 2^−6 | *< 2^(−10^5)* | |
| `20×Comm. [Kb]` | 1.94 | 2.99 | 4.86 | 2.17 | 2.36 | 3.13 | | |
| Brute force | 2^168 | 2^168 | 2^170 | 2^81 | 2^134 | 2^205 | *2^80* | *2^103* |
| **Kernel** | **2^106** | **2^122** | **2^138** | **2^64** | **2^81** | **2^128** | *2^577* | *2^844* |
| Big `m` | 2^108 | 2^205 | 2^399 | 2^113 | 2^135 | 2^243 | *2^461k* | *2^997k* |
| Syndrome | 2^118 | 2^312 | 2^1002 | 2^151 | 2^172 | 2^339 | *2^252k* | *2^530k* |
| Sub-matrices | ∞ | ∞ | ∞ | ∞ | ∞ | ∞ | ***2^97*** | ***2^114*** |
| MQ | ∞ | ∞ | ∞ | ∞ | ∞ | ∞ | *2^152* | *2^188* |

Bold is the source's own bolding: the best attack. The last two columns are **not challenges** —
they are the MinRank instances arising in the Kipnis–Shamir attack on HFE, included "for
comparison", and they are italicised here to keep them out of the challenge set.

**This supersedes the second-hand table in #205's body**, which came via `MinRank2.0`'s Table 1 and
a search summary. It agrees on every challenge parameter. Two differences are worth recording:

- The two HFE columns are over **`q = 2^80` and `q = 2^103`**, not `q = 2`. #205's reading of
  Courtois's thesis recorded `q = 2` for those columns. `2^80` is what `asia01` prints and is the
  mathematically expected value — Kipnis–Shamir lifts HFE to the degree-`n` extension — so the
  thesis reading should be re-checked before anything is built on it. Flagged, not resolved: I did
  not read the thesis.
- `MinRank2.0`'s Table 1 labels the matrix dimensions `m, n` and the unknown count `k`. Courtois
  labels the dimensions `η, n` and the unknown count `m`. **Same numbers, rotated names.** The
  fixture uses Courtois's names, since it transcribes Courtois.

### 2.3 The table checks out against its own paper

A transcription deserves an independent check, and `asia01` supplies one. §10 derives

```
m_max = ηn + r² − (η + n)r + 1
```

as the largest `m` "such that we expect to have one solution on average", from an expected count of
`((q^m − 1)/(q − 1)) · q^(−(η−r)(n−r))` non-collinear solutions. Applied to the printed parameters:

| | A | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| `m_max` | 10 | 10 | 10 | 82 | 122 | 197 |
| printed `m` | 10 | 10 | 10 | 81 | 121 | 190 |
| expected solutions | ≈2^0 | ≈2^0 | ≈2^0 | ≈2^0 | ≈2^0 | 2^−6 |
| printed `Pr_α[Rank ≤ r]` | 0.6 | 0.6 | 0.6 | 0.6 | 0.6 | **2^−6** |

All six reproduce. A, B and C sit exactly on `m_max`; D and E sit one below it, which still yields
≈1 expected solution because the `q − 1` divisor is 1 over `GF(2)`; F sits seven below, and the
expectation lands on `2^−6` — **the printed value, exactly**. One expected solution gives
`1 − 1/e = 0.63`, printed as `0.6`.

This is machine-checked. `tests/minrank_challenges.rs` re-derives the probability column from
`q, η, n, m, r` and requires it to reproduce what the fixture prints, so corrupting any one of those
five fields fails a test with a specific message rather than silently changing what a future
surrogate generator would build.

### 2.4 `k = 9` versus `k = 10`, reconciled

`FauSafSpa10` works with challenge C as `(n, k, r) = (11, 9, 8)` — nine unknowns. Courtois prints
`m = 10`. `MinRank2.0` prints `k = 10`. The gap is exactly one degree of freedom, and it is the one
Courtois's own non-collinearity count removes: his expected-solution formula counts combinations
`Σ αᵢ Mᵢ` **up to scalar**, dividing `q^m` by `q − 1`. `FauSafSpa10` instead works in the
"well-defined" case `k = (n − r)²`, which for A, B and C is `(6−3)² = (7−4)² = (11−8)² = 9` — the
case where the determinantal locus is zero-dimensional and FGLM applies.

So `(11, 9, 8)` is challenge C after one unknown is pinned, and `(11, 10, 8)` is the challenge as
Courtois states it. **Neither source is wrong; they are different normalisations of the same
challenge, and #206 must pick one explicitly rather than inherit whichever it read last.** The
practical consequence is in `FauSafSpa10` §5.3, which exploits precisely this: it specialises `s`
further variables and solves `65521^s` over-determined `(11, 9 − s, 8)` systems.

---

## 3. Provenance: where the instances are not

### 3.1 `minrank.org` — the corrected reachability record

#205's body recorded the host as a parked domain. Its first comment already corrected that, and
this section records the settled state so the question is not reopened. Verified 2026-11-07 from
the Wayback CDX index and from #205's live probes:

| fact | evidence |
|---|---|
| HTTPS is broken | no certificate matches the hostname |
| the root is parked | `http://www.minrank.org/` is a frameset redirecting to `cryptosystem.net` |
| **deep paths still serve original content over plain HTTP** | `/hfe` (76 982 B), `/challenge1.txt` (1 511 654 B), `/phd.pdf` (1 490 144 B) all return 200 |
| the MinRank challenge files are not among them | `/minrank/`, `minrank.html`, `challenge.txt`, `minrankchal.txt`, `mr.txt` → 404; `cryptosystem.net/minrank/` → a 195-byte error page |

So: **the front door is dead, the site is not, and the MinRank challenge files are specifically
absent.** The surviving `challenge1.txt` is the *HFE* Challenge 1 input system, a different family
(#198), and `signature-based.md:490` already records it.

### 3.2 The archived official page carries no data

This is the decisive check, and it had not been done. `asia01`'s header names
`http://www.minrank.org/minrank/` as the scheme's "Official web page". The Wayback Machine has
**eight 200-responses** for that exact URL — 2001-05-05, 2001-06-06, 2001-08-16, 2001-12-18,
2002-08-25, 2002-10-09, 2003-01-08, 2003-08-15 — growing from 1 325 to 1 705 bytes.

Both ends were fetched and read in full. The
[2003-08-15 capture](https://web.archive.org/web/20030815093642/http://www.minrank.org/minrank/) is
a one-screen page titled "The MinRank Zero-knowledge Authentication Method". Its entire link set is
papers and navigation: `rump00.pdf`, the Crypto 2000 rump programme, the PKC&CNT page, the Asiacrypt
2001 conference page, `eprint.iacr.org/2001/058{,.ps,.pdf}`, `asia01.pdf` (the Asiacrypt slides), and
sibling cryptosystem pages. The
[2001-05-05 capture](https://web.archive.org/web/20010505141225/http://www.minrank.org/minrank/) is
the same page, shorter, under the title "The MinRank Algorithm".

**No challenge file, no challenge table, no data link, in any capture across two and a half years —
the whole lifetime of the page.** A CDX prefix enumeration of `www.minrank.org/minrank*` returns
only that page, a `301` for the slashless form, and two `302` GIFs.

The Asiacrypt slides `asia01.pdf` were also fetched from Wayback
(`edac46d9049527eb093437dacef110d955830ff4b488a7f05893baa2865c5197`, 1 111 346 B, 20 pp.) and are a
**scan with no text layer** — `pdffonts` reports no fonts and every page is CCITT/JPEG imagery. They
were not OCR'd; they are a slide deck of a paper already read in full, so the expected marginal
value is low. Recorded as not examined.

### 3.3 Leads closed, and by whom

| lead | outcome | by |
|---|---|---|
| `minrank.org` live deep paths | challenge files 404; HFE files survive | #205 comments |
| Courtois's PhD thesis (`minrank.org/phd.pdf`) | parameters present, **matrices absent** | #205 comments |
| `minrank.org/minrank/` official page, 2001–2003 archives | **papers and slides only; no data** | this document, §3.2 |
| `asia01` / ePrint 2001/058, the original publication | **"six sets of parameters"; no data, no prize** | this document, §1 |
| `FauSafSpa10`, the 2010 paper on C | **generated its own random instances** | this document, §5.1 |
| `MinRank2.0`, the 2026 paper on D | **solved "an instance"**, and ships it | this document, §5.2–5.3 |
| Asiacrypt 2001 slides | scan, no text layer; not OCR'd | this document, §3.2 |

### 3.4 Verdict, per challenge

| | parameters | authentic instance | status in the literature |
|---|---|---|---|
| **A** | **verified** (`asia01` §4.3) | **none published** | reported solved 2008; see §9 |
| **B** | **verified** | **none published** | reported solved 2008; see §9 |
| **C** | **verified** | **none published** | method + cost published 2010 (`FauSafSpa10`); see §5.1 on what "solved" means |
| **D** | **verified** | **none published**; one third-party same-parameter instance exists (§5.3) | solved 2026 on a generated instance (`MinRank2.0`) |
| **E** | **verified** | **none published** | open |
| **F** | **verified** | **none published** | open |

Nothing in this table rests on secondary literature except the status column, which is marked as
such in §9.

---

## 4. The published generation construction

`asia01` §5.1, verbatim:

> The public key are `1 + m` matrices `η × n` over a finite field `GF(q)`, `M₀; M₁, …, M_m`. Let
> `r < n`. To generate a random hard instance we pick `1 + m − 1` (pseudo-)random matrices
> `M₀; M₁, …, M_{m−1}`. We chose a random `M` of rank `r` and we "adapt" `M_m`. For this we pick a
> random `α ∈ GF(q)^m` such that `α_m ≠ 0` and `M_m` is computed as:
> `M_m = (M + M₀ − Σ αᵢ Mᵢ)/α_m`

which plants `Σ_{i=1..m} αᵢ Mᵢ − M₀ = M`, of rank exactly `r`. And:

> In practice, we generate `M` and `M₁, …, M_{m−1}` out of a pseudo-random generator with a seed of
> 160 bits. It is better to pick all `Mᵢ` invertible, but it's not necessary. We may use the
> well-known LU method to generate a deterministic pseudo-random invertible matrix. In order to
> generate `M`, first we generate a matrix `L` which is random invertible `r × r`, completed with
> 0's to an `η × n` matrix. Then a random couple of invertible matrices `S` and `T` is applied
> `M = SLT`.

Three consequences.

1. **#205's research question 5 guessed this nearly right, and differs in two ways.** The guess
   omitted `M₀`, and it drew the rank-`r` matrix `R` freely. The published construction includes
   `M₀` in the adaptation and builds `M = S·L·T` from an invertible `r × r` block, i.e. **exactly
   rank `r`, never below**. Use the published form.
2. **The instances were meant to be reproducible, and the reproduction key was not published.** "a
   pseudo-random generator with a seed of 160 bits" — neither the seed nor the generator is named
   anywhere in the paper. This is the sharpest statement of the provenance verdict: the author
   described a deterministic recipe and published neither of the two things needed to re-run it.
   **An instance cannot be recovered by recomputation, and any attempt would be a fabrication.**
3. Courtois's own footnote 5 is the caveat to carry into any surrogate: the construction "is
   believed to give hard instances most of the time… It might change if a better way to produce hard
   instances is known."

---

## 5. What the solving papers actually solved

This section exists because "challenge C was solved in 2010" and "challenge D was solved in 2026"
are both true in a weaker sense than they sound, and the difference is the whole point of #205.

### 5.1 `FauSafSpa10` and challenge C

**They generated their own instances.** §5.2, verbatim:

> Generation of the instances. For `(n, k, r) ∈ ℕ³`, we generate a `n × n` matrix `M = Mᵢ,ⱼ` where
> the `Mᵢ,ⱼ` are affine linear forms in `k` variables: `Mᵢ,ⱼ = a⁽⁰⁾ᵢ,ⱼ + Σ a⁽ˡ⁾ᵢ,ⱼ xˡ`, where the
> `a⁽ˡ⁾ᵢ,ⱼ` are chosen uniformly at random in `GF(65521)`.

Uniform random affine forms — not Courtois's planted construction, and certainly not published
matrices. Their Table 1 column for `(11, 9, 8)` is a *generic* instance of challenge C's shape.

**The full solve was a projection, not an execution.** §5.3 and Table 2 specialise `s` variables and
solve `65521^s` over-determined `(11, 9 − s, 8)` systems. The reported choice is `s = 1`:

| `s` | 3 | 2 | **1** | 0 |
|---|---:|---:|---:|---:|
| minors F5 time | 79 s | 1 594 s | **80 255 s** | 2 570 396 s |
| `d_reg` | 9 | 10 | **13** | 25 |
| log₂ ops | 73 | 60 | **49.1** | 40.2 |

and then, verbatim:

> In practice, the 65521 computations of the over-determined systems can be parallelized, and the
> total number of required arithmetic operations (2^49.1) is quite practical. **We estimate to 238
> days the time needed to effectively solve this challenge on 64 quadri-core processors.**

So what was executed is **one** `s = 1` system — 80 255 s and 29 929 MB — and what is published is
the extrapolation `2^49.1 = 65521 × (ops for one system)` plus a 238-day projection that was not
run. The conclusion's "This method is feasible in practice since it requires only `2^49` arithmetic
operations" is a feasibility claim, which the paper is entitled to make; it is not a report of a
completed solve.

**Two figures in #205's comments are misattributed and are corrected here.** The "14 days on one
CPU (with Maple) … 12 hours on 24 CPU" is `FauSafSpa10` §5.1, the cost of **computing the `(r+1)`-
minors** — generating the 3 466 MB algebraic system — and not of solving anything. And the `2^49`
is the projected total, not a measured one.

Units, kept separate as #205 requires: `2^49.1` **arithmetic operations in `GF(65521)`**; `80 255 s`
and `29 929 MB` for one sub-system, measured; `238 days on 64 quadri-core processors`, estimated.
These are three different kinds of claim and none converts into another here.

For #206: the minors route reaches `(11, 9, 8)` at `d_reg = 25` against Kipnis–Shamir's `2^64.4`
estimate, so minors beats KS on this instance by the paper's own numbers — but `r + 1 = 9`, so the
minors are `9 × 9`, which #206 already records as out of reach of a cofactor expansion.

### 5.2 `MinRank2.0` and challenge D

From the ePrint abstract page, verbatim (the PDF 403s; the abstract page does not):

> With the improved attack, we solved Courtois challenge~D, open since 2001: **an instance** over
> `𝔽₂` with `19 × 19` matrices, `81` unknowns, and target rank `10`, solved in 11434 CPU days, an
> estimated `2^61` bit opetations. [*sic*]

"**an instance**" — indefinite article, in the authors' own abstract. The parameters quoted match
`asia01`'s D column exactly (`19 × 19`, `m = 81`, `r = 10`, `q = 2`), and §5.3 shows the artifact
generating its own.

Units, again kept apart: `11434 CPU days` is measured; `2^61 bit operations` is estimated. They are
not the same claim and neither is derivable from the other without a model.

### 5.3 The one instance file that exists

The artifact repository named in #205 resolves. Its HTML endpoint returns `401 not_connected`, but
its JSON API serves a file listing and file bodies:

```
https://anonymous.4open.science/api/repo/MinRank_Kernel_Search-0BF4/files/
https://anonymous.4open.science/api/repo/MinRank_Kernel_Search-0BF4/file/<path>
```

It contains `F2Matrix.{cpp,hpp}`, `MRutils.{cpp,hpp}`, `main.cpp`, `KernelSearch.magma`, a
`Makefile`, a `README.md`, `LICENSE`, and **`paper_instance/instance.txt`**.

| | |
|---|---|
| file | `paper_instance/instance.txt` |
| sha256 | `2fc12a0d52fc2523e773153b50b1b643b545506b2181b63505ec1d6ab084bda9` |
| size | 60 774 B, 1 559 lines |
| format | line 1 is the header `19 19 81 10` = `η n m r`; then `1558 = 82 × 19` rows of 19 space-separated `0`/`1` entries |
| contents | **82** matrices `19 × 19` over `GF(2)` — `M₀` and `M₁…M₈₁`, confirming the inhomogeneous formulation of §2.1 |
| licence | **GPL-3.0** (repository `LICENSE`) |
| accessed | 2026-11-07 |

The `README.md` confirms the generation story outright:

> `./main generate [file] [m] [n] [r] [k] [seed]` — Builds a MinRank instance with a known rank-`r`
> solution … All of `m`, `n`, `r`, `k` default to `19 19 10 81` (**Courtois challenge D**).

So the 2026 result's own tooling treats "Courtois challenge D" as a **parameter default**, exactly
as this document concludes in §1.

**This file is not committed here and must not be.** It is GPL-3.0; committing it into an MIT crate
is the redistribution problem `external-provenance-policy.md` §4 exists to prevent, and
`fukuoka-mq.md` §3 already set the precedent of pinning a SHA-256 instead of vendoring bytes.
**And it must not become a fetch-script dependency**: `anonymous.4open.science` is an
anonymized-submission host whose URLs expire on publication. The SHA-256 above is recorded so that
if the file reappears in a named repository, the bytes can be shown to be the same ones.

Note for whoever picks this up: the repository `README.md` credits six authors — Aragon, Bros,
**Cheemalakonda**, Perlner, Smith-Tone, Verbel — while the ePrint page lists five, without
Cheemalakonda. Unresolved; probably an anonymized-submission version differing from the preprint.

---

## 6. Corrections to the record

Collected so they are not buried.

1. **The verifier needs `M₀`.** The condition is `Rank(Σ αᵢ Mᵢ − M₀) ≤ r`, over `1 + m` matrices.
   #205's motivation and #195's self-verification argument both state it without `M₀`. The argument
   survives — it is still one rank computation — but an implementation written from the issue text
   would be wrong. (§2.1)
2. **The HFE comparison columns are over `2^80` and `2^103`, not `2`.** (§2.2)
3. **`FauSafSpa10`'s 14-day/12-hour figure is the cost of computing the minors, not of solving.**
   (§5.1)
4. **`FauSafSpa10`'s `2^49` is a projection**, from one executed sub-system; the 238-day figure was
   never run. "Challenge C was solved in 2010" overstates what that paper reports. (§5.1)
5. **Nobody solved a Courtois instance, because there are none.** Both the 2010 and the 2026 results
   are on generated same-parameter instances. (§5)
6. **`minrank.org` is not a dead host**; its front door is. (§3.1)

### 6.3 One row that does not check out

The brute-force row is `q^m · O(rηn)` to within rounding for A, B, C, E and F:

| | A | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| `log₂(q^m · rηn)` | 166.8 | 167.6 | 169.9 | **92.8** | 133.1 | 203.6 |
| printed | 168 | 168 | 170 | **81** | 134 | 205 |

**D is the sole outlier**, and `2^81` is exactly `q^m` with the polynomial factor dropped. This is my
arithmetic, not a claim by the paper, and I did not find an erratum. It matters only if the
brute-force row is used as a difficulty scale for D; the kernel row, which is the row the paper
bolds as best, is unaffected. Recorded rather than corrected.

---

## 7. Registry proposal

**Nothing is registered by this document**, and that is the recommendation, not an omission.
`src/grobner/research/challenge.rs`'s `registry()` is frozen by `test_the_registry_is_frozen` and
every entry in it is a problem that **is** a file with a digest. There is no file to digest for any
of A–F, so an entry today would have to describe a surrogate that does not yet exist, and the
`digest` field would be over bytes nobody has generated. That is precisely the conflation #205 is
written to prevent.

What a future F2 should register, when a generator exists:

| id | class | significance | objective | notes |
|---|---|---|---|---|
| `courtois-minrank-A-surrogate-<seed>` | `Engineering` | `SurrogateWitness` | **new** `MinRank { eta, n, m, r }` | `GF(65521)`, 11 matrices `6×6`, `r = 3`. Smallest member. |
| `courtois-minrank-C-surrogate-<seed>` | `Engineering` | `SurrogateWitness` | same | `GF(65521)`, 11 matrices `11×11`, `r = 8`. The reproduction target: `FauSafSpa10` publishes a method and a cost for this shape. |
| `courtois-minrank-D-external` | — | — | same | **record only**, not an instance in the corpus: §5.3's file, pinned by SHA-256, not redistributed, not fetched by script. |
| E, F | — | — | — | **do not register.** Unattempted and out of reach; `GF(2)` blocks on #196 G2. |

Three schema requirements this family imposes, all of which belong to #73 (A4) rather than here:

1. **A new `Objective`.** `rank(Σ αᵢ Mᵢ − M₀) ≤ r` is neither `CicoExact` nor `MqRoot`. It carries a
   target rank, which no existing objective has. (`additional-benchmarks.md` §6.3 reached the same
   conclusion for LowMC.)
2. **A `ChallengeParameters::MinRank` variant** carrying `(q, η, n, m, r)` and the generator seed —
   the seed is what makes a surrogate reproducible, and it is the one thing Courtois did not publish
   about his own.
3. **A way to record a published figure in its own unit.** §5 produced five figures in four units
   for two challenges. `fukuoka-mq.md` and `additional-benchmarks.md` §6.2 both hit this gap; this
   family makes it acute.

**Recommended single target for F2: challenge C's shape.** `GF(65521)` needs no new field
arithmetic beyond one `PrimeFieldElement32<65521>` declaration, the witness check is one rank
computation, and `FauSafSpa10` publishes `d_reg`, ideal degree, operation counts and timings for
both modellings at exactly `(11, 9, 8)` — four independent quantities a Zeebra run can be checked
against without any of them being a timing comparison. A's shape is the smoke test on the way.

---

## 8. What is in the repository

| path | what it is |
|---|---|
| `research/minrank/courtois-challenges.tsv` | the §2.2 table, machine-readable, with the source and its SHA-256 in the header |
| `tests/minrank_challenges.rs` | eight tests over that fixture |

The fixture is **parameters, and its header says so twice**. The tests are not a parse check: they
re-derive the probability column from `q, η, n, m, r` (§2.3), require `m ≤ m_max`, require the
kernel row to be the cheapest finite attack on every challenge as the source bolds it, require
sub-matrices and MQ to be infinite throughout, and require D's row to match the §5.3 instance
header, including that `1558 = (81 + 1) × 19` — the `+1` being `M₀`.

Each was confirmed to fail on a corrupted fixture: changing A's `r` from 3 to 4, F's `m` from 190 to
189, D's `q` from 2 to 65521, or C's kernel exponent from 138 to 1138 each produces a named failure.
A silent transcription error is the failure mode this fixture would otherwise have.

No field was declared, no instance generated, no system solved, and no measurement recorded.

---

## 9. Secondary-only, and uncertain

**Recorded in secondary literature only.** The following are from `MinRank2.0` as quoted in #205's
comments. Its PDF 403s here, Wayback has no capture of it, and its abstract page — which does
resolve — does not contain them. **I did not verify these and they must not be treated as checked:**

- A and B "were solved by Faugère, Levy-dit-Vehel, and Perret in 2008". Plausible and consistent
  with `FauSafSpa10`'s §1 ("the challenges A and B proposed in [7]"), but the 2008 paper was not
  read.
- "Challenge C was solved in 2010 by [27], and again in 2015 by Steel [41] with an improved
  implementation." §5.1 shows the 2010 half overstates what `FauSafSpa10` reports. **The 2015 Steel
  reference is the most likely record of an executed solve of C and was not pursued** — it is the
  single highest-value unread source on this issue.
- "Challenges D, E, and F have remained unsolved for 25 years."
- `MinRank2.0`'s Table 1 itself. §2.2 replaces it with the original.

**Uncertain or not established.**

- Whether Courtois ever distributed instances privately — by email, in the thesis defence, or to
  correspondents. §3 establishes only that none was *published*. This is unfalsifiable from here and
  is recorded as such rather than as a negative.
- The `q = 2` versus `q = 2^80` discrepancy between `asia01` and #205's reading of the thesis (§2.2).
- The author-list discrepancy for `MinRank2.0` (§5.3).
- D's brute-force row (§6.3).
- The Asiacrypt 2001 slides are a scan and were not OCR'd (§3.2).
- `web.archive.org` returned "Temporarily Offline" intermittently throughout this work. Every
  Wayback result quoted here was fetched successfully and is reproducible by URL; but a reader who
  gets an error page should retry rather than conclude the capture is gone.

**Attempted and failed, with what was tried.** `https://eprint.iacr.org/2026/2733.pdf` → `403`
(the abstract page at the same host returns `200`, so this is PDF-specific, matching
`elimination-beyond-grobner.md` §8). Wayback CDX for `eprint.iacr.org/2026/2733*` → the service was
offline on each attempt; not retried to exhaustion. `https://anonymous.4open.science/r/…` HTML →
`401 not_connected`; the JSON API under `/api/repo/…` works and is what §5.3 used.
