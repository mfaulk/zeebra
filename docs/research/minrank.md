# Courtois MinRank challenges A–F: the parameters, and the instances that never existed

**Measured at:** not measured here — every figure is quoted from the literature or from a challenge record
([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

Reference for F1 (#205) and F1b (#382), under the MinRank epic #195. Consumes the provenance
conventions of `docs/research/external-provenance-policy.md` §9 and the redistribution discipline of
`docs/research/fukuoka-mq.md` §3.

#382 added §5.4 and rewrote §9. If you are here for one question — *did anyone ever actually run a
solve of challenge C?* — the answer is **yes, once: Allan Steel, 23 August 2014, on a generated
same-parameter instance, in about 30 hours on one CPU core and one GPU**, reported at PASCO 2015.
§5.4 has the evidence and the three ways that sentence is usually got wrong.

**Sources of record.** Each read in place rather than through a search summary, with the bytes
pinned. The first four are primary and were read in full; the last two are reachable only in part,
and every claim resting on them says so.

| short name | what it is | how it was obtained | sha256 | accessed |
|---|---|---|---|---|
| **`asia01`** | Courtois, *Efficient Zero-knowledge Authentication Based on a Linear Algebra Problem MinRank*, Asiacrypt 2001, LNCS 2248 pp. 402–421; IACR ePrint 2001/058 | `eprint.iacr.org` PDFs 403 here, so the Wayback Machine's capture of the author's own ePrint PDF: [`web.archive.org/web/20040723070613id_/http://eprint.iacr.org/2001/058.pdf`](https://web.archive.org/web/20040723070613id_/http://eprint.iacr.org/2001/058.pdf) | `bbdfe4521eb102eb7dc137bea245f2a6ec186ee9fddf2b5b906a2cbfc0daee34` (256 966 B, 19 pp.) | 2026-11-07 |
| **`phd`** | Courtois, *La sécurité des primitives cryptographiques basées sur des problèmes algébriques multivariables : MQ, IP, MinRank, HFE*, thèse de doctorat, Université Paris 6, soutenue 25 septembre 2001 | the scheme's own host still serves it over plain HTTP (§3.1): [`http://www.minrank.org/phd.pdf`](http://www.minrank.org/phd.pdf) | `b907bced0836298381e22dc025758296a40da57def87f50c7cb84e41e7a02e9d` (1 490 144 B, 221 pp.) | 2026-11-07 |
| **`FauSafSpa10`** | Faugère, Safey El Din, Spaenlehauer, *Computing Loci of Rank Defects of Linear Matrices using Gröbner Bases and Applications to Cryptology*, ISSAC 2010 | author mirror, [`members.loria.fr/PJSpaenlehauer/data/papers/FauSafSpa10a.pdf`](https://members.loria.fr/PJSpaenlehauer/data/papers/FauSafSpa10a.pdf) | `eeb0330b0490c6296c5b33d2515b84b072358ca7a883e141b548bff0fda201ad` (146 591 B, 8 pp.) | 2026-11-07 |
| **`Steel14`** | Allan Steel, *A Dense Variant of the F4 Gröbner Basis Algorithm* (December 2013), carrying the update *Minrank Challenge C Solved Directly* (August 2014) and a further update of July 2015 — the author's own page on the Magma site, linked from his homepage | [`http://magma.maths.usyd.edu.au/users/allan/densef4/`](http://magma.maths.usyd.edu.au/users/allan/densef4/) | `7eb1b3566bcb002f2ead1bc8626116a10123a30c646002d7f6f6bcfbf6fd4c71` (16 854 B of HTML) | 2026-11-07 |
| **`Steel15`** | Allan Steel, *Direct solution of the (11,9,8)-MinRank problem by the block Wiedemann algorithm in magma with a tesla GPU*, PASCO '15, Bath, 10 July 2015, pp. 2–6, [doi:10.1145/2790282.2791392](https://doi.org/10.1145/2790282.2791392) | **abstract only.** Closed access; `dl.acm.org` 403s here and Unpaywall reports no OA copy. Bibliographic record from Crossref and from Sydney's own publication list; abstract text from OpenAlex (§9) | — | 2026-11-07 |
| **`MinRank2.0`** | Aragon, Bros, Perlner, Smith-Tone, Verbel, *Cryptanalysis of MinRank 2.0*, IACR ePrint 2026/2733 | **abstract page only**; the PDF still 403s and Wayback has no capture (§9) | — | 2026-11-07 |

Licensing, per `external-provenance-policy.md` §4: `MinRank2.0` is **CC BY** (stated on its ePrint
page). The artifact repository in §5.3 is **GPL-3.0** and its data is therefore *not* redistributed
here. `asia01`, `phd`, `FauSafSpa10` and `Steel14` are read as publications; nothing is copied from
any of them.

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

- The two HFE columns are over **`q = 2^80` and `q = 2^103`**, not `q = 2`.
- `MinRank2.0`'s Table 1 labels the matrix dimensions `m, n` and the unknown count `k`. Courtois
  labels the dimensions `η, n` and the unknown count `m`. **Same numbers, rotated names.** The
  fixture uses Courtois's names, since it transcribes Courtois.

**The thesis/paper `q` discrepancy was an artifact, and is closed.** #205 recorded Courtois's thesis
as printing `q = 2` for the two HFE columns where `asia01` prints `2^80` and `2^103`, and the
previous revision of this document left that open. It was a text-extraction artifact, exactly the
one this section's own first paragraph warns about. `phd` Table 24.7.1 (p. 183, PDF page 183) was
rendered as an image and read: it prints **`2^80` and `2^103`**, and `pdftotext` drops those
exponents onto the preceding line, where a reader scanning the flattened `q` row sees `… 2 2 2 2 2`
and counts eight twos. **There is no discrepancy between `asia01` and `phd`.**

Reading the thesis page also buys a free check on the whole of §2.2. `phd` Table 24.7.1 reproduces
`asia01` §4.3 **cell for cell across all eight columns and all twelve rows, including the source's
own bolding** — Kernel bold on A–F, Sub-matrices bold on the two HFE columns. The table above is
therefore transcribed from one primary document and confirmed against a second, independently
typeset one. One cosmetic difference, recorded so nobody reports it as a conflict: in `phd` the
`Pr_α[Rank ≤ r]` entry `< 2^(−10^5)` is a **single cell merged across both** HFE columns, where the
table above puts it under *HFE Chall. 1* and leaves *Quartz* blank.

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
| the thesis's own parameter table, read as an image | confirms §2.2 cell for cell; the `q = 2` reading was a `pdftotext` artifact | this document, §2.2 |
| `minrank.org/minrank/` official page, 2001–2003 archives | **papers and slides only; no data** | this document, §3.2 |
| `asia01` / ePrint 2001/058, the original publication | **"six sets of parameters"; no data, no prize** | this document, §1 |
| `FauSafSpa10`, the 2010 paper on C | **generated its own random instances** | this document, §5.1 |
| `Steel14`/`Steel15`, the "2015 Steel" reference | identified; **an executed solve of a C-shaped instance, 23 August 2014**; no instance published | this document, §5.4 |
| `MinRank2.0`, the 2026 paper on D | **solved "an instance"**, and ships it | this document, §5.2–5.3 |
| Asiacrypt 2001 slides | scan, no text layer; not OCR'd | this document, §3.2 |

### 3.4 Verdict, per challenge

| | parameters | authentic instance | status in the literature |
|---|---|---|---|
| **A** | **verified** (`asia01` §4.3, confirmed against `phd` §24.7) | **none published** | `FauSafSpa10` Table 1 runs A's shape `(6, 9, 3)` in 1.1 s and attributes solving A to its [14] = the 2008 paper; see §9 |
| **B** | **verified** | **none published** | same, for B's shape `(7, 9, 4)`, 37 s; see §9 |
| **C** | **verified** | **none published** | **solved by execution, 23 August 2014**, on a generated same-parameter instance (`Steel14`, reported in `Steel15`). The 2010 result is a method plus a projection — §5.1, §5.4 |
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
| minors F5 time | 79 s | 1 594 s | **80 255 s** | *2 570 396 s* |
| minors F5 mem | < 1 000 MB | 2 400 MB | **29 929 MB** | — |
| `d_reg` | 9 | 10 | **13** | *25* |
| log₂ ops | 73 | 60 | **49.1** | *40.2* |

**The paper marks its own estimates, and that is what licenses the reading above.** Table 2's
caption says, verbatim:

> The values in italic font were not effectively computed but are given as estimates based on
> practical and theoretical results.

Italics here reproduce the source's. The page was rendered as an image to read them, because the
distinction is carried entirely by the typeface and `pdftotext` discards it. **Only the `s = 0`
column is italic.** So `80 255 s`, `29 929 MB` and `d_reg = 13` at `s = 1` are the paper's own
measurements of a run that happened, and `2 570 396 s` and `d_reg = 25` at `s = 0` are not. The
`log₂ ops` row is one step removed in both cases: the caption defines it as
`log₂(65521^s · OpF5)`, an estimate of the cost of the **whole** challenge, so `49.1` is an executed
`OpF5` scaled by `65521`, and `40.2` is an interpolated one.

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

**The door `FauSafSpa10` left open is the one that was eventually walked through** (§5.4). Its
closing remark on `s = 0` — solving the challenge directly, with no exhaustive search at all — is,
verbatim:

> Note that it may be possible to compute directly a Gröbner basis of the ideal generated by the
> minors (`s = 0`). By interpolating the practical results, we give a rough estimate of the
> complexity of this computation: it would take approximately 29 days (on one CPU). However, it is
> not clear how much memory would be required, and the FGLM step could be untractable since the
> degree of the ideal is 259545 (Corollary 1).

Two things to carry forward. The "approximately 29 days" is the table's italic `2 570 396 s`
restated — `2 570 396 / 86 400 = 29.75`, my arithmetic on two of the paper's own figures, not a
third figure. And the stated obstacle is **FGLM**, not the Gröbner step: `deg(I) = 259545` and FGLM
is cubic in it. That is precisely the obstacle §5.4 removes.

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

### 5.4 Steel 2014/2015 and challenge C: the one solve that was actually executed

This section answers #382. The short form: **yes — someone ran it to completion, and it was neither
2010 nor, strictly, 2015.** Allan Steel solved a challenge-C-shaped instance on **23 August 2014**,
on one CPU core and one GPU, and reported it at PASCO 2015.

**Identifying the reference.** `MinRank2.0` says C was solved "again in 2015 by Steel [41] with an
improved implementation". Its bibliography could not be read — the PDF 403s and Wayback still has
no capture (§9) — so **[41] is identified by content, not by reading the entry**, and that is the
one inferential step in this section. The identification is safe because the target is unique:
searching both OpenAlex and Crossref for works by Allan Steel on MinRank returns **exactly one**,
`Steel15`; it is dated 2015; and "an improved implementation" describes it precisely. Its
bibliographic record is confirmed twice over, from
Crossref's registration metadata and from the University of Sydney's own
[2015 publication list](https://www.maths.usyd.edu.au/u/pubs/publist/pubs2015.html):

> Allan Steel (2015). Direct Solution of the (11,9,8)-MinRank problem by the Block Wiedemann
> Algorithm in Magma with a Tesla GPU. The 7th International Workshop on Parallel Symbolic
> Computation (PASCO), … PASCO '15, ACM, ISBN 978-1-4503-3599-7, 2–6.

**The run, in the author's own words.** `Steel14` — Steel's page on the Magma site, which his
homepage links as "**NEW:** Minrank Challenge C Solved Directly (August 2014)" — says, verbatim:

> In 2014 I have developed code within Magma for the Wiedemann algorithm for computing the minimal
> polynomial of large sparse matrices. Using this, **on 23 August 2014 I managed to solve a random
> instance over GF(65521) of the Cortois [*sic*] Minrank Challenge C where `(n,k,r)=(11,9,8)`**,
> using the direct approach with the Wiedemann algorithm (that is, without using the above
> evaluation method).
>
> The current times for this direct method are:
> - Dense F4: 7.0 hours [computes the grevlex GB of the zero-dimensional ideal; the GB has 51275
>   polys with up to 48620 terms each].
> - Wiedemann: 23.2 hours [computes the minimal polynomial of a 259545 by 259545 matrix with
>   density 13.4%].
>
> This is using just one Intel E5-2687W (3.1GHz) core and a Tesla C2075 GPU (same as above).

and, under "Update (July 2015)":

> Details on the computation (which can now be done in 15.1 hours with just one core and a K40
> Tesla GPU) can be found in my PASCO 2015 paper.

`Steel15`'s abstract agrees and is the published form of the claim:

> As a result, the Magma implementation can directly solve a 16-bit **random instance** of the
> Courtois (11,9,8)-MinRank Challenge C in about 15.1 hours with a single Intel Sandybridge CPU
> core coupled with an Nvidia Tesla K40 GPU.

**This is `s = 0` — the route `FauSafSpa10` raised and set aside.** The cross-check is exact and is
the reason this is worth trusting: Steel's Wiedemann step computes the minimal polynomial of a
**259545 × 259545** matrix, and `259545` is `FauSafSpa10`'s `deg(I)` for `(11, 9, 8)` from its
Corollary 1 — the very number it cited as the reason FGLM "could be untractable" (§5.1). Steel did
not make FGLM tractable; he replaced it. `Steel15`'s abstract says what with:

> We show how some very large multivariate polynomial systems over finite fields can be solved by
> Gröbner basis techniques coupled with the Block Wiedemann algorithm, thus extending the
> Wiedemann-based 'Sparse FGLM' approach of Faugère and Mou.

**Two independent computations, fifteen years and two codebases apart, agree on the degree of this
ideal to the digit.** For F2 (§7) that is a checkable quantity of a quality the timing rows do not
have. (`Steel14` writes "the Wiedemann algorithm" where the 2015 title and abstract say "Block
Wiedemann"; whether the 2014 run used the block variant is not stated on the page.)

**It is still a generated same-parameter instance, so §1 stands unchanged.** "A random instance over
GF(65521) … where `(n,k,r)=(11,9,8)`" is the same kind of object `FauSafSpa10` and `MinRank2.0`
used. `Steel14` publishes no instance file, no seed and no generator; probing the site for one under
seven spellings (§9) returns 404 throughout, and the
page's one offer of input files — "[Links for the actual input files will be added soon.]", about
the HFE systems — was never redeemed. **There is still no downloadable MinRank object with challenge
parameters other than the challenge-D file of §5.3.**

**Note the normalisation.** `(n, k, r) = (11, 9, 8)` is §2.4's nine-unknown form, not Courtois's
`m = 10`. Steel solved the shape `FauSafSpa10` defined, which is C with one unknown pinned. #206
must say which it means.

**Steel's separate, and still projected, figure for the evaluation route.** Before the direct solve,
the same page compares Magma's dense F4 against `FauSafSpa10` on the `s = 1` route:

> Faugere et al estimated that a single instance … takes 80255 seconds using Faugere's F5 code, so
> the challenge can be solved in about 166.7 core years, or in about 238 days on a 256-core Xeon
> cluster. With the dense variant of F4 in Magma V2.20 …, a single instance … takes 1637 seconds, so
> the challenge can be solved in about 3.4 core years, or in about 4.8 days on a 256-core cluster.

**That half is a projection too** — one sub-instance measured, `× 65521`, exactly as in §5.1, and
nobody ran 65521 of them. It is recorded here so it is not mistaken for the solve. Every derived
number in it reproduces (my arithmetic): `80 255 × 65521 = 5.258 × 10⁹ s = 166.6` core-years, which
on 256 cores is 237.7 days — so Steel reads `FauSafSpa10`'s "64 quadri-core processors" as 256 cores
and lands on its 238 days; `1 637 × 65521 = 1.073 × 10⁸ s = 3.40` core-years and 4.85 days on 256
cores; and `80 255 / 1 637 = 49.0`, Steel's "about 50 times faster".

One wording difference, recorded rather than resolved: Steel writes that Faugère et al.
"**estimated**" the 80 255 s, where `FauSafSpa10`'s own italic convention marks that figure as
effectively computed (§5.1). Nothing here turns on it — the 80 255 s is used identically either way
— but a reader comparing the two sources will meet it.

**Units, kept apart as §5.1 and §5.2 do.** The 2014 run: `7.0 h` dense F4 **plus** `23.2 h`
Wiedemann, **measured**, on 1 core of an Intel E5-2687W (3.1 GHz) with one Tesla C2075 — 30.2 hours
of wall clock in total (my addition). The 2015 run: `15.1 h`, **measured**, on 1 Intel Sandybridge
core with one Tesla K40. Neither is an operation count, and neither is comparable to
`FauSafSpa10`'s `2^49.1` arithmetic operations without a model. Whether the two Steel runs are
comparable to each other is settled by the paper, below: they are three runs of one system on three
hardware configurations.

#### The paper, read at source

`Steel15`'s five pages were closed access through #382 and #404 and were supplied by the owner on
**2026-11-08**. It is still closed access and **not redistributable**, so the PDF is read from
outside the repository and nothing of it is committed here beyond quotation. Everything §5.4 said
from the abstract and from `Steel14` survives; the paper adds the stage breakdown, resolves two of
§9's uncertainties, and contradicts the page on one figure.

**Table 2, Challenge C, all times in seconds.** Three runs of the *same* system: CPU only, CPU with
the C2075, CPU with the K40.

| stage | CPU | CPU + C2075 | CPU + K40 |
|---|---:|---:|---:|
| GB (dense F4) | 302 442 | 24 358 | 19 745 |
| BW data | 406 207 | 51 550 | 19 674 |
| BW LLL | 10 928 | 9 490 | 9 295 |
| BW det | 4 659 | 4 644 | 4 627 |
| BW total | 421 794 | 65 693 | 33 596 |
| eval GB | 3 743 | 1 275 | 979 |
| **total** | **727 979 (202.2 h)** | **91 326 (25.4 h)** | **54 320 (15.1 h)** |

**The 15.1 h is the same instance re-run, not a fresh one.** §9 recorded this as unknown, and the
paper says it plainly: "We were first able to solve a random instance with our Magma implementation
on 23 August 2014, using the above CPU with the C2075 GPU in about 25 hours computation. Since then,
we have also been able to use a K40 GPU, so that is why timings for both types of GPUs are
provided." The three columns are one computation measured three ways, so the 202.2 h CPU-only figure
is also not a separate result.

**The 2014 run used the block variant.** §9's second uncertainty. There is one implementation in the
paper and it is Coppersmith's block algorithm throughout, with blocking parameter `m = 800`,
`ε = 6`, and precision `P = ⌈2N/m⌉ + ε = 655` data-collection steps — and it is "our Magma
implementation" that solved the instance on 23 August 2014. `Steel14`'s bare "Wiedemann" is the
page being loose, not a different algorithm. The paper does not separately describe the 2014 code,
so this is the authors' own framing rather than a second witness.

**The page and the paper disagree about the C2075 run, and neither dates its figures.** `Steel14`
gives `7.0 h` dense F4 plus `23.2 h` Wiedemann on one E5-2687W core with a C2075 — 30.2 h. The
paper's C2075 column is 6.77 h, 18.25 h and 0.35 h, totalling **25.4 h**, and its text calls the
23 August 2014 run "about 25 hours". So the paper's figures are 1.19x faster in total on hardware
described identically, with no Magma version and no measurement date attached to either set. Which
set belongs to the August 2014 run is not determinable from the two documents; the paper's own prose
points at its own column. This is the defect #335 is about, in someone else's record.

**Table 1, the `(r + 3, 9, r)` ladder, and what is comparable in it.** Times in seconds; the Magma
columns are the CPU-with-K40 runs.

| `r` | degree of `I` | density of `A` | F-M GB | F-M sol | Magma GB | Magma sol | `m` | memory |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | 4 116 | 23.0% | 14 | 9 | 14 | 9 | 40 | 0.4 GB |
| 5 | 14 112 | 19.0% | 240 | 272 | 55 | 73 | 100 | 1.3 GB |
| 6 | 41 580 | 16.9% | 4 041 | 5 715 | 388 | 580 | 200 | 12.1 GB |
| 7 | 108 900 | 14.8% | — | — | 3 129 | 4 781 | 400 | 39.2 GB |
| 8 | 259 545 | 13.4% | — | — | 19 745 | 34 575 | 800 | 191.1 GB |

The `r = 8` row is Challenge C and reconciles with Table 2: `19 745 + 34 575 = 54 320 s = 15.1 h`.
**The F-M columns are not measurements on Steel's machine** — they are Faugère and Mou's published
times on a 2.5 GHz Intel E5420, which Steel rescales by `2.5/3.1` for comparison. A cross-library
ratio formed from them carries that rescaling, which is the kind of thing
`external-comparison-protocol.md` §7 refuses; Steel labels it, and so must anyone quoting it.

**The structural data, which is the part worth having.** The symbolic MinRank matrix's minors take
about 1 280 s on every version and yield a zero-dimensional ideal `I ⊂ K[x₁…x₉]`, `K = F₆₅₅₂₁`, with
**3 025 generators each of total degree 9**. Its grevlex GB has **51 275 polynomials of maximum
degree 25 with up to 48 620 terms each** and costs **137 GB**. `A`, multiplication by `x₉ + I` on
`R/I`, is `259 545 × 259 545` at **13.42%** density with 221 690 unit-vector rows and **37 855 dense
rows**, so the compact representation is a `37 855 × 259 545` dense `B` taking 1 166 s to build and
**73.2 GB** to store. Peak memory for the whole computation is **191.1 GB**.

**It is internally consistent, which is checkable rather than assumed.** Each of the 655 steps does
a `[800 × 37 855] · [37 855 × 259 545]` product and a `[800 × 259 545] · [259 545 × 800]` product,
and Table 3 gives the per-step cost as 618.2 s (CPU), 76.7 s (C2075) and 28.1 s (K40). Against the
BW-data totals, with the 1 166 s setup added (my arithmetic): `655 × 618.2 + 1 166 = 406 087` against
406 207; `655 × 76.7 + 1 166 = 51 405` against 51 550; `655 × 28.1 + 1 166 = 19 572` against 19 674.
Three for three inside 0.5%.

**A third independent agreement on the degree.** §5.4 already notes `259 545` appearing in both
`FauSafSpa10` and Steel. Table 1's degree column and `FLP08`'s solution counts (§5.5) now agree
where they overlap — `4 116` at `r = 4` and `14 112` at `r = 5` — so the sequence
`980, 4 116, 14 112, 41 580, 108 900, 259 545` for `r = 3…8` is corroborated across two codebases
and seven years. For #206 that is a far better anchor than any timing row here.

**And the field size barely matters.** The paper closes by noting the same computation runs in
roughly the same time over `F₂¹⁶` as over `F₆₅₅₂₁` on the CPU — "about a week" CPU-only — because a
Magma matrix multiplication over `GF(2^16)` costs about what one over `F_p` through ATLAS does.

**So what is the honest status of challenge C?** Three claims, which the literature tends to merge:

| claim | status |
|---|---|
| "C was solved in 2010" | **overstated.** `FauSafSpa10` executed one `s = 1` sub-system and projected the rest (§5.1) |
| "C was solved again in 2015 by Steel" | **true in substance, off by a year in fact.** The execution was 23 August 2014; PASCO 2015 is where it was published, with a faster time |
| "someone has run a challenge-C-parameter MinRank solve to completion" | **true, once, by Steel, on 23 August 2014, on one core and one GPU.** The run took "about 25 hours" by the paper's account and 30.2 h by the page's; the same system was later re-run at 15.1 h on a K40 and at 202.2 h with no GPU at all |

### 5.5 `FLP08` and challenges A and B: the 2008 authors, reporting their own runs

The one acceptance item #382 left open, and #404's second half. Faugère, Levy-dit-Vehel and Perret,
*Cryptanalysis of MinRank*, CRYPTO 2008, LNCS 5157 pp. 280–296, was unobtainable from this machine
through both issues and was supplied by the owner on **2026-11-08**. Closed access and **not
redistributable**: quoted here, not committed.

**The attribution is now first-hand.** §9 recorded the A/B claim as resting on `FauSafSpa10` §1
citing this paper — a primary source attributing a result to someone else. The paper itself says it:

> Challenges A `(6, 9, 3)` and B `(7, 9, 4)` are completely broken. We emphasize that such sets of
> parameters were the most suited for a practical use of the ZK authentication scheme proposed in
> [8].

So the provenance grade for A and B rises from *attributed by a primary source* to *reported by the
authors who ran it*, which is what #382's acceptance asked for. No status elsewhere in this document
changes — A and B were never in doubt as breakable.

**It also corroborates §1 at source, for A and B.** The paper generates its own instances, by the
construction §4 describes: random `(M₁ … M_k)` and random `(λ₁ … λ_k)` with `Σλᵢ ≠ 0`, a random
`M` of rank `r`, and `M₀ = Σ λᵢ(Mᵢ − M)`. The first published break of A and B therefore used a
**generated same-parameter instance**, exactly as `FauSafSpa10`, `MinRank2.0` and Steel did. Every
executed result on these challenges is now confirmed at source to be of that kind.

**Where the `k = 9` normalisation comes from.** §2.4 reconciles Courtois's `m = 10` with the
literature's nine unknowns, and this paper is the origin: by its Lemma 1 it fixes `Δ = 1` variable
for A and B and `Δ = 2` for C, so A becomes `k = 9, n = 6, r = 3` with 18 equations in 18 unknowns,
B becomes `k = 9, n = 7, r = 4` (21 in 21) and C becomes `k = 9, n = 11, r = 8` (33 in 33). The
convention every later paper inherits is stated here, with its reason.

**The figures, from Fig. 1.** `F5` and `FGLM` as implemented in C in **FGb**, on several 3.2 GHz
Xeon bi-processors with 64 GB of RAM, instances generated in Maple, with Magma 2.14 used for some
bases. `T_DRL` is the degree-order GB, `T_FGLM` the conversion, `s` the number of `λᵢ` fixed by
exhaustive search, `D` the number of solutions over the algebraic closure, `d_reg` the maximum
degree reached.

| | A `(6, 9, 3)` | B `(7, 9, 4)` | `(8, 9, 5)` |
|---|---:|---:|---:|
| `s = 0`, FGb: `T_DRL + T_FGLM` | 30.0 + 34.8 = **64.8 s** | 3 794 + 2 580 = **6 374 s** | 328 233 s |
| `s = 0`, Magma 2.14 | 300 + 200 = 500 s | 48 745 + **∞** | **∞** |
| memory (`F5`) | 406.5 MB | 3 113 MB | 58 587 MB |
| `log₂ N` | 30.5 | 37.1 | 43.4 |
| `d_reg` | 5 | 6 | 7 |
| `D` | 980 | 4 116 | 14 112 |
| `s = 3`, FGb `T_DRL` | 0.05 s | 1.0 s | 15.6 s |

**Two things in that table are worth not misreading.** First, **Magma 2.14's FGLM did not terminate
on B** (`∞`), where FGb's did in 2 580 s — so "A and B are completely broken" rests on FGb, and the
one place the paper offers a cross-implementation comparison it is not a race Magma finished.
Second, the `s = 3` row is **one sub-system**, not the challenge: the exhaustive-search route costs
`#K^s` systems, which for C at `s = 3` is 65 521³ of the 56 987 s rows. That is the same
sub-instance-times-field-size projection §5.1 and §5.4 both guard against, and the paper is explicit
that C "seems intractable with the current implementation".

**The record's A/B times were the 2010 paper's, not the 2008 result.** §9 quoted 1.1 s and 37 s for
`(6, 9, 3)` and `(7, 9, 4)` from `FauSafSpa10`'s Table 1. The 2008 authors' own figures for the same
shapes are **64.8 s and 6 374 s** — 59x and 172x slower, on 2008 hardware with a different modelling
(Kipnis–Shamir here, minors there). Both make the point that A and B are trivial; they are not the
same measurement, and the 2008 numbers are the ones the 2008 claim is based on.

**Two incidental results, recorded because they are cheap and checkable.** The paper observes
`d_reg = max(r + 2, 4)` across its experiments — a prediction #206 can test against this crate — and
reports its own complexity estimate for C at `2^88`, which is the figure `FauSafSpa10`'s minors
modelling later improved to `2^49.1` (§5.1). An attack estimate falling by `2^39` across two papers
is a modelling difference, not a machine one.

---

## 6. Corrections to the record

Collected so they are not buried.

1. **The verifier needs `M₀`.** The condition is `Rank(Σ αᵢ Mᵢ − M₀) ≤ r`, over `1 + m` matrices.
   #205's motivation and #195's self-verification argument both state it without `M₀`. The argument
   survives — it is still one rank computation — but an implementation written from the issue text
   would be wrong. (§2.1)
2. **The HFE comparison columns are over `2^80` and `2^103`, not `2`** — in `asia01` *and* in the
   thesis. The previous revision of this document left an `asia01`-versus-thesis conflict open on
   this row; there is none. #205's `q = 2` reading was `pdftotext` dropping the superscripts, and
   the rendered page says `2^80`/`2^103`. **This corrects a correction**, and closes the question.
   (§2.2)
3. **`FauSafSpa10`'s 14-day/12-hour figure is the cost of computing the minors, not of solving.**
   (§5.1)
4. **`FauSafSpa10`'s `2^49` is a projection**, from one executed sub-system; the 238-day figure was
   never run. "Challenge C was solved in 2010" overstates what that paper reports. The paper's own
   italic convention in Table 2 now backs this: the `s = 1` column is roman (computed), the `s = 0`
   column italic (estimated). (§5.1)
5. **Nobody solved a Courtois instance, because there are none.** The 2010, 2014 and 2026 results
   are all on generated same-parameter instances. (§5)
6. **`minrank.org` is not a dead host**; its front door is. (§3.1)
7. **Challenge C *has* been solved by execution — on 23 August 2014.** Not in 2010, and not quite
   in 2015 either: `Steel15` (PASCO 2015) is where the 2014 run was published, with a faster
   re-reported time. This supersedes the previous revision's §9, which recorded the Steel reference
   as unpursued and the executed status of C as unknown. (§5.4)
8. **`FauSafSpa10`'s `deg(I) = 259545` for `(11, 9, 8)` is independently confirmed.** Steel's
   executed Wiedemann step computes the minimal polynomial of a `259545 × 259545` matrix. Two
   codebases, fifteen years apart, same digit. (§5.4)

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

**It is not a typesetting slip in one document.** `phd` Table 24.7.1 prints `2^81` for D's
brute-force entry as well (§2.2), so the figure is whatever Courtois intended it to be, twice.

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
| `courtois-minrank-C-surrogate-<seed>` | `Engineering` | `SurrogateWitness` | same | `GF(65521)`, 11 matrices `11×11`, `r = 8`. The reproduction target: `FauSafSpa10` publishes a method and a cost for this shape, and `Steel14` ran one to completion (§5.4). |
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

**§5.4 strengthens this recommendation rather than adding to it.** It does not add a fifth
quantity — `Steel14` publishes wall clock, which is the one kind of figure this corpus does not
compare against. What it adds is that one of the four is now **double-sourced**: `deg(I) = 259545`
is both derived from `FauSafSpa10`'s Corollary 1 and measured by an executed computation that had
to build a `259545 × 259545` matrix to finish. A Zeebra run on a C-shaped surrogate that reports a
different ideal degree is wrong, and that is now known from two directions rather than one.

It also settles the framing question #382 was filed to answer: a C-shaped solve **reproduces a
result**, it does not extend a projection. The honest caveat is that it reproduces *Steel's* result
on *Steel's* kind of instance — a random one — and no two random `(11, 9, 8)` instances have to
cost the same.

---

## 8. What is in the repository

| path | what it is |
|---|---|
| `research/minrank/courtois-challenges.tsv` | the §2.2 table, machine-readable, with both primary sources and their SHA-256s in the header |
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

**The four claims this section carried, and where each stands after #382.** They came from
`MinRank2.0` as quoted in #205's comments; its PDF still 403s and Wayback still has no capture, so
its bibliography remains unread.

| claim | status now |
|---|---|
| "Challenge C was solved in 2010 by [27], and again in 2015 by Steel [41] with an improved implementation." | **resolved, and both halves need qualifying.** §5.1 for 2010; §5.4 for Steel — an executed solve, dated 23 August 2014, published at PASCO 2015. Read at `Steel14`, the author's own page, and in `Steel15`'s five pages since 2026-11-08. [41] identified by content, not by reading the bibliography entry (§5.4) |
| A and B "were solved by Faugère, Levy-dit-Vehel, and Perret in 2008" | **resolved, read at source.** The 2008 paper was obtained on 2026-11-08 and says it in its own words — "Challenges A `(6, 9, 3)` and B `(7, 9, 4)` are completely broken" — with its own figures, machine and instance-generation construction (§5.5). The attribution no longer rests on `FauSafSpa10` §1 quoting it, and the 1.1 s / 37 s this row used to carry are that 2010 paper's minors-modelling times, not the 2008 result's 64.8 s and 6 374 s |
| "Challenges D, E, and F have remained unsolved for 25 years." | **still secondary-only, and now partly contradicted by `MinRank2.0` itself**, whose abstract reports solving D (§5.2). Read as a statement about the position before that paper. E and F unexamined here |
| `MinRank2.0`'s Table 1 itself | **superseded.** §2.2 replaces it with the original, now confirmed against a second primary document |

**Uncertain or not established.**

- Whether Courtois ever distributed instances privately — by email, in the thesis defence, or to
  correspondents. §3 establishes only that none was *published*. This is unfalsifiable from here and
  is recorded as such rather than as a negative.
- `Steel15`'s abstract places Magma V2.20's release in "late 2014"; `Steel14` says "released
  December 2013". The five pages now read say "released in version V2.20 in late 2014" **twice**, in
  the introduction and in §2, so the abstract is not a stray phrase and the contradiction is between
  two documents by the same author. Magma's own release-note pages return `401` to this machine.
  Nothing in §5.4 or §5.5 depends on it.
- Which of the two C2075 figure sets — the page's 30.2 h or the paper's 25.4 h — is the 23 August
  2014 run. The paper's prose fits its own column; neither document dates its measurement or names a
  Magma version (§5.4).
- Whether the 2014 code was the block variant on its own terms. The paper's one implementation is
  Coppersmith's block algorithm and it is the one that solved the instance, which is the authors'
  framing rather than a separate statement about the 2014 run (§5.4).
- Steel describes `FauSafSpa10`'s 80 255 s as "estimated" where that paper's own typography marks it
  computed (§5.4). Recorded, not resolved; no figure here turns on it.
- The author-list discrepancy for `MinRank2.0` (§5.3).
- D's brute-force row (§6.3) — now known to read `2^81` in both `asia01` and `phd`, so not a
  one-document slip, but still unexplained.
- The Asiacrypt 2001 slides are a scan and were not OCR'd (§3.2).
- `web.archive.org` returned "Temporarily Offline" or `429` intermittently throughout this work and
  throughout #382's. Every Wayback result quoted here was fetched successfully and is reproducible
  by URL; a reader who gets an error page should retry rather than conclude the capture is gone.

**Resolved since the previous revision.** The `q = 2` versus `q = 2^80` question (§2.2) — closed,
and there never was a conflict. Both closed-access sources below were supplied by the owner on
2026-11-08 and read: `Steel15`'s five pages (§5.4) and the 2008 CRYPTO paper (§5.5). That closes
#404 and with it the last acceptance item of #382. Neither PDF is redistributable and neither is in
the repository; what they say is here, and `research/minrank/courtois-challenges.tsv` is unchanged
because neither paper carries challenge data.

**Attempted and failed, with what was tried.**

| target | what was tried | result |
|---|---|---|
| `MinRank2.0` full text, to read entry [41] | `https://eprint.iacr.org/2026/2733.pdf`; `/archive/2026/2733/…` | `403` both, while the abstract page at the same host returns `200` — PDF-specific, matching `elimination-beyond-grobner.md` §8 |
| `Steel15` full text (PASCO 2015, 5 pp.) | `dl.acm.org/citation.cfm?id=2791392`, `dl.acm.org/doi/10.1145/2790282.2791392`, `doi.org/…` | `403` from `dl.acm.org` on all three. Unpaywall: `is_oa: false`, no OA locations. OpenAlex: `oa_status: closed`. **Closed access, and no free copy exists to find — obtained from the owner on 2026-11-08 and read; see §5.4.** Everything this document had said from the abstract and from `Steel14` survived the reading. Before it arrived: bibliographic record from Crossref and Sydney's publication list, abstract from OpenAlex's inverted index, checked gapless and duplicate-free over positions 0–147 |
| Faugère–Levy-dit-Vehel–Perret, *Cryptanalysis of MinRank*, CRYPTO 2008, LNCS 5157 pp. 280–296 | `iacr.org/archive/crypto2008/51570280/51570280.{pdf,ps}` → `403`; `link.springer.com/chapter/10.1007/978-3-540-85174-5_16` → `303` to an `idp.springer.com` login; `www-polsys.lip6.fr/~jcf/Papers/…` → connection timed out twice; HAL → one record, `hal-00976374`, **metadata only, no file**; Unpaywall and OpenAlex → closed, no abstract indexed | **obtained from the owner on 2026-11-08 and read; see §5.5.** Every route from this machine failed, which is why #404 existed. With it, #382's last acceptance item closes |
| a published instance file for challenge C | `Steel14`'s host, at `densef4/magma/`, `densef4/minrank`, `densef4/minrank.txt`, `densef4/MinRank`, `densef4/input/`, `densef4/mr`, `densef4/chalC.txt` | `404` throughout; `gb/magma/` is `403` (listing denied, individual files serve). No instance, no seed, no generator published |
| Wayback captures of `dl.acm.org`'s page for the DOI, to read the abstract at the publisher | CDX for `dl.acm.org/citation.cfm*` filtered on `2791392`, and prefix CDX for the `/doi/` form | `504` and `503 Temporarily Offline`; retried later and got `429`. Not retried to exhaustion — the abstract was obtained by another route, so this was not needed |
| `anonymous.4open.science` HTML (§5.3) | `/r/…` | `401 not_connected`; the JSON API under `/api/repo/…` works and is what §5.3 used |
