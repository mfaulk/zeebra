# M27 — Competitive MQ Solving

**Measured at:** publication bound `2205c7db`…`5e1b8ea9` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](research/external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

**Status:** integration report published in [§15](#15-integration-report-2026-11-11); retained
library-scope Minimum and Strong met. Broader studies remain open.
**Prerequisite at planning:** M26 was incomplete (historical §0). Its
[integration report](MILESTONE-ALGORITHMIC-ELIMINATION.md#14-integration-report-2026-11-11)
now exists; §15 scores M27 independently against its retained criteria.
**Plan written against:** commit `d9121c0` (`merge: render the scoreboard without measuring, and
record the rf4-rp2 witness`), rebased onto `74cb43a` after #435 and #448 merged mid-planning.
**Board:** [Zeebra, project #7](https://github.com/users/mfaulk/projects/7), label `M27`.
**Epic:** #450.

M25 added the axis that produced Zeebra's first measured deficits. M26 spent one of them and, in
spending it, produced a measurement that reframes the other: **the F4 gap is not a stage.** Against
Singular it is — 4.13x on `mq-random-10`, spanned by final interreduction's 80.4%. Against
Groebner.jl it is 348x, and making interreduction *entirely free* leaves 68x of it standing.

M27's unit of progress is therefore **a completed externally specified instance, or a competitive
gap closed against the engine that actually sets the pace** — and the second half of that sentence
is new. M26 was allowed to choose its target by Amdahl arithmetic over one comparand. M27 may not,
because the arithmetic now says the comparand was the wrong one.

### Revision history

| date | change |
|---|---|
| 2026-11-11 | #458 integrates retained results in §15, scores §10 after #668, regenerates the board, and records the M28 recommendation. Earlier sections retain the planning and intermediate evidence. |
| 2026-11-07 | Written at `d9121c0` from M26's landed work, #447's cross-engine screen, and `f4-resource-scaling.md` §10.4. M26's §13 report does not exist yet; §0 records what that costs this plan. |
| 2026-11-07 | **#452 and #471 implemented** (PRs #476, #478). #452's counters settle #440's four-way verdict as **copy-bound** — 1.17 billion terms rewritten at 64.2x amplification, where swell is only 8.8x and 22.6 M divisor tests cannot be 35 s — and correct §4's inference, which had read Groebner.jl's 604 as a term count when it is a column count. #471 then measured **4.18x end to end** with bases asserted equal, clearing §10's Strong criterion. Two findings M27-0 must carry: the §3 baseline does not reproduce (four stages within 4.4%, interreduction 54% higher, so the share is 86.7% and the ceiling 7.52x), and the §4 cost estimate was 24x out because Zeebra's autoreduce matrix has **405x** the cells Groebner.jl's does — now #477. |
| 2026-11-07 | **#447 answered** (`a1867a7`, `docs/research/groebner-jl-gap.md`) **and M27-A's shape changed with it.** The counts agree — both engines reach 10 batches, 11 matrices, 247 basis elements and quotient dimension 354 — so gate 0's "Zeebra does asymptotically more work" branch is **dead**, and the 344x decomposes into **4.89x** randomized linear algebra (declined by policy), **5.03x** interreduction done as 247 divisions where Groebner.jl uses one Macaulay matrix, and **14.0x** a per-operation constant uniform to 11.6x-25.5x across every other stage. Final interreduction is **13 871x** behind; the next worst stage is 97.1x. So M27-A's first item is no longer a faster `normal_form` but **matrix-based interreduction** (§5.2a), and the JIT caveat is settled at ~2%. |
| 2026-11-07 | **#435 merged during planning** (`25e10fe`), so §1.1's figures were re-read from `main`'s five-library board at cohort `7adb29e` rather than from #447's issue body. Three consequences: Singular's wall on that cohort is 7 001.1 ms, not the 7 291 ms M25 recorded, which moves the Singular-parity requirement from 14.5x to **17.7x** on interreduction; Sagebrush's ratio is marked **non-authoritative by the board** and is demoted to context; and the board stores `process-wall 7.35 s` beside Groebner.jl's `solve 83.4 ms`, an 88x gap against which Zeebra is **3.95x faster** — which sharpens #447's first question rather than softening it. Also records #448's resolution (`a062b59`), which explains the board-membership discrepancy the first draft hedged against. |

---

## 0. M26 is unfinished, and this plan is written around that

**Planning snapshot:** the statements below describe `d9121c0`, not the report snapshot.
For current results and remaining work, see §15.

M26's plan document still reads `**Status:** planned.` It has no report section, no criterion-by-criterion
scoring, and four commits, all dated 2026-11-07. Thirteen of the M26 epic's twenty sub-issues are
open. **M27 is therefore planned against a moving baseline, and the honest response is a measurement
gate rather than an assumption.**

What has landed and is *not* recorded in M26's plan:

| landed | the figure | where it is recorded |
|---|---|---|
| the Euclidean remainder sequence in `src/` | **2 094x** at order 1 458 (137x at 162, 649x at 486); fitted exponent **1.8452** against dense's 2.9431 ± 0.0183 | `structured-sylvester.md:370-392` |
| #351's root finding at degree 59 049 | `roots` **153.2 s** — **46% below** the ~285 s extrapolation; deflation **0.50 s** | `graeffe-root-finding.md:1988-2016` |
| #304 / #437, basis held once | `mq-random-10` **29 919 → 29 011 ms**, ~3% | commit `92a262d` |
| #395 / #409, `max_wall_time` honored during interreduction | — | commit `e6161d6` |

*One row — the `rf4-rp2` Poseidon witness and its scoreboard record — was moved out with the
cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

What has **not** landed, and what each absence costs M27:

- **#370, M26's report.** No criterion is scored. M27-0 cannot inherit a conclusion it must instead derive.
- **#369 / PR #435 — resolved during planning, and this plan was rewritten around it.** As first
  drafted, §1.1's entire comparand table existed only in an unmerged pull request, and no workstream
  could have quoted it. **#435 merged at `25e10fe`**, so `research/competitive/results/history.json`
  now holds **252 rows across five libraries** — `zeebra` 72, `singular` 72, and 36 each for
  `msolve 0.11.0`, `groebner.jl 0.10.11 (julia 1.11.7)` and
  `sagebrush 86d9f1c7` — with the `7adb29e` cohort carrying the figures §1.1 uses. The figures below
  are read from `main`. #435 still reports **#369's acceptance item 2 as unmet**, and for a reason M27
  inherits directly: the ~30x msolve conversion deficit is not reproducible as a record, because
  msolve refuses an eliminant at the corpus characteristic. That is the argument driving #426 — §5.4.
- **#368, M26-B's Krylov conversion.** No stage-1 characterization is on record. M27 schedules no
  FGLM work; see §3.
- **#318 / #319, the drift bounds.** Nowhere recorded as resolved. `README.md:3465-3467` still says
  the figures on record are ~1.2x faster than today's and that the 2.868 ms order-162 anchor does
  not reproduce. **Every ratio M27 computes across that boundary carries a ~20% systematic**, which
  is M26's Rule 3 and is inherited unchanged.
- **`README.md`'s Status list.** Has no bullet for the Euclidean remainder sequence, the `rf4-rp2`
  witness, or #304. M26-I's "the board and documentation truthful" criterion is unmet in the one
  file a reader opens first. Not M27's to fix — it is #370's — but M27-0 may not freeze a baseline
  from it.

**Consequence, stated once.** M27-0 is unconditional and runs first. Every other workstream's
*measurement* half is gated on it; the parts of each workstream that are correctness fixes or
capability work are not, and start immediately. §8 has the schedule.

---

## 1. Prior evidence, and the four rules it imposes

M26 imposed three rules. Its own work added a fourth, and it is the one that reorganizes this
milestone.

**Rule 1 — memory is measured before a run is authorized, not estimated after it.** Inherited. The
six-round symbolic build was predicted at ~68 MB and measured at **57.0 GB**, 838x.

**Rule 2 — a stage share is not a speedup.** Inherited, and strengthened: a stage share may be
called a ceiling under Amdahl and may **never** be called a speedup. Any end-to-end claim is
measured end to end.

**Rule 3 — a figure taken today is not comparable to a figure on record.** Inherited, and still
live because #318/#319 are unresolved.

**Rule 4 — an Amdahl ceiling computed against one comparand says nothing about another.** This is
new, and #447 is the measurement that forces it. M26 screened every F4 candidate against Singular's
4.13x and concluded interreduction "spans it". That conclusion is correct and it is also
*parochial*: the same stage share, screened against the engines M25 provisioned and M26 never
populated the board with, rules out the entire F4 optimization program as a route to parity. §1.1
does the arithmetic.

### 1.1 One stage, five comparands, two completely different conclusions

`mq-random-10`, `reduced-grobner-basis`, grevlex, one digest, all pairs agreeing on quotient
dimension, basis cardinality and leading-monomial count (#447):

| engine | wall | board's published ratio | peak RSS |
|---|---:|---:|---:|
| **zeebra** | **29 011.4 ms** | — | 163.5 MB |
| singular | 7 001.1 ms | **4.14x**, 3 invariants agreed | 23.9 MB |
| Sagebrush | 334.9 ms | 86.63x, 3 invariants agreed, **not authoritative** | 32.0 MB |
| msolve | 243.1 ms | **119.32x**, 2 invariants agreed | 12.3 MB |
| **Groebner.jl** | **83.4 ms** | **347.83x**, 3 invariants agreed | 726.3 MB |

All five at digest `72d0ad315fc2`, cohort `7adb29e`, one worker. **Sagebrush's ratio is marked
non-authoritative by the board itself** — "sagebrush may not be a speedup denominator" — so it is
context, not a competitive claim, and M27 does not quote it as one.

#349's split, over three runs with identical pairs (1 777), batches (10) and basis size (247):
interreduction **80.4%**, elimination 13.9%, construction 3.5%, symbolic 1.4%, extraction 0.4%.
Amdahl ceiling **5.10x**.

**That split is pre-#437 and is labelled so throughout this document.** #304/#437 removed two copies
of the basis from the stage #349 measured and moved the row 29 919 → 29 011 ms. The duplication it
removed was in `minimize_grobner_basis`, which #436 measured at **0.06%** of the stage by time, so
the share is expected to be substantially unchanged — but *expected* is not *measured*, and M27-0
re-takes it (§5.1). Every use of 80.4% and 5.10x below inherits that caveat.

Now make interreduction free — not faster, *free*:

> 29 011.4 ms x 0.196 = **5 686 ms**. Against Groebner.jl's 83.4 ms that is **68x behind**; against
> msolve **23x**; against Sagebrush **17x**. Against Singular it is **1.23x ahead.**

So, precisely:

| target | what interreduction must do | reachable? |
|---|---|---|
| **2x end to end** (29 011 → 14 506 ms) | 23 325 → 8 820 ms, **2.64x faster** | plausibly, and it is M27-A's target |
| parity with Singular (7 001 ms) | 23 325 → 1 315 ms, **17.7x faster** | only by an asymptotic change |
| parity with msolve or Groebner.jl | — | **not at any interreduction speedup** |

**Singular's 4.13x is spanned by one stage. The other three gaps are not.** That is the first
evidence in this repository that the F4 problem is not a stage, and it is why M27-A opens with a
question about *how much work Zeebra does* rather than about how fast it does it.

### 1.1a Answered: the gap is three factors, and only one of them is a stage to speed up

**#447 is closed and `docs/research/groebner-jl-gap.md` is the finding.** It changes this section's
conclusion in the direction that matters, so the arithmetic above is kept for the record and
superseded here.

**The counts agree.** Same digest, grevlex: **10 matrix batches**, **11 matrices**, **1 777 against
1 787 selected pairs** (0.6% apart), **247 basis elements**, **quotient dimension 354**. The only
material difference is reducer rows — 84 645 against 47 464, a factor of 1.78, of which Groebner.jl's
own trace says 41.5% were ever used. **Zeebra does the same work and takes 344x longer**, so gate 0's
leading candidate — "asymptotically more work, and no data-structure change closes it" — is dead.

| factor | size | what it is | M27's disposition |
|---|---:|---|---|
| **A** | **4.89x** | Groebner.jl's default *randomized* linear algebra | **Declined by policy.** Zeebra commits to a deterministic kernel; #269/§6.6's verdict stands and its magnitude was understated ~20x |
| **B** | **5.03x** | final interreduction by **247 iterated divisions** where Groebner.jl does **one Macaulay matrix** | **M27-A's first item.** §5.2a |
| **C** | **14.0x** | a per-operation constant, uniform at **11.6x–25.5x** across every other stage | #317's, and only #317's. §5.2 |

`4.89 × 5.03 × 14.0 = 344x`, against a measured 344x.

**The per-stage split is what makes B unmistakable:**

| stage | Zeebra | Groebner.jl | ratio |
|---|---:|---:|---:|
| symbolic preprocessing | 403.16 ms | 15.8 ms | 25.5x |
| construction + elimination + extraction | 5 292.44 ms | 54.5 ms | 97.1x |
| pair selection + bookkeeping | 81.07 ms | 6.96 ms | 11.6x |
| **final interreduction** | **24 136.08 ms** | **1.74 ms** | **13 871x** |
| F4 total | 29 912.76 ms | 79.0 ms | 379x |

Three stages between 11.6x and 97.1x is an implementation constant. One at nearly fourteen thousand
is **not an implementation of the same thing at all** — and the stage split is now measured four
times, unmoved, at 80.4%/80.69%.

Three caveats travel with every figure in that table.

**The Groebner.jl figure is an inner time, and the board stores what it excludes.** The same row
records `process-wall 7.35 s` and `process-cpu 8.16 s` beside `solve 83.4 ms` — an **88x** gap, and
against that process wall Zeebra at 29.01 s is **3.95x faster**. The adapter measures `@solve_ns`
around the `groebner` call after a discarded proxy solve in the same ring, with residual compilation
measured at ~0.17 ms absolute and signed so as to *overstate* Groebner.jl's time; its 726.3 MB peak
is the Julia process's, a cost of deployment rather than the algorithm's working set. **#447 settled the JIT question**: three
successive timed calls span **2.2%** and the sign inflates Groebner.jl, so ratios at this size are
good to ~2%. Separately, Groebner.jl's 9.33 ms of AbstractAlgebra conversion sits inside the board's
`@solve_ns` and outside `f4!`, which makes the board's 348x the **conservative** reading — stripping
it gives ~386x.

**Sagebrush is not a speedup denominator**, by the board's own marking and by
`external-comparands.md`'s maturity gate. Its row is context.

**Groebner.jl is GPL-2.0**, itself an adaptation of GPL-2.0+ msolve with GPL-3.0+ code embedded:
**algorithmic reference only, no line may enter an MIT core** (`groebner-jl-implementation.md` §7,
#274).

### 1.2 The Fukuoka resource stop is stale, and its own research document says the question is open

*This section (the Fukuoka challenge frontier finding) was moved out with the cryptanalysis research
in #668; it is preserved at commit 9532a9a2.*

### 1.3 Two claims in circulation that this plan corrects

**"Eliminating the interreduction bottleneck closes the competitive gap."** It closes the Singular
gap and overshoots it. It does not touch the gap against the three engines that are 17x–348x ahead.
M27-A is funded as a **2x end-to-end improvement and an Amdahl-ceiling exhaustion**, not as parity.

**"#268 is ruled out."** #268 is ruled out *as an explanation of the 4.13x*, on the evidence that
symbolic + construction are **4.9%** of `mq-random-10`. That screen does not cover the monomial
representation's cost **inside the 80.4% stage**, where `subtract_shifted` performs one
`Monomial` multiply and one `MonomialOrder::cmp` per merged term, `MonomialOrder::cmp` is a `match`
per comparison rather than monomorphized, and grlex and grevlex each recompute `degree()` on both
operands by summing `[u32; N]`. Three independent engines converge on packing a monomial into one
word so that a degree comparison is one instruction — msolve's divmask, Groebner.jl's seven
encodings, Sagebrush's 148-line `order.rs`.

**#268's own latest comment narrows its ruling in the same direction, and names the instance.**
Magma's `SetSparseMonomialMinRank` default is **20 variables** and `mq-random-10` has **ten**, so
"the ruling should stand for what it measured and no further" — with the suggested disposition being
to re-scope #268 toward finding the crossover on **`fukuoka-mq-III-n20-seed0`**, whose harness
already exists from #304/#305. That is M27-B's target instance. **So M27-A's representation question
and M27-B's frontier instance converge on one measurement**, and §8 sequences them rather than
letting two agents discover it separately. The reopening for interreduction is #317's (§5.2); the
20-variable crossover is #268's, and neither is #268 being reinstated as an explanation of the 4.13x.

---

## 2. Objectives

1. *An objective on a published challenge instance was moved out with the cryptanalysis research in
   #668; it is preserved at commit 9532a9a2.*
2. **Deliver a measured 2x end-to-end improvement on `mq-random-10`** with a bit-identical reduced
   basis, or a recorded verdict naming the measured term that refuses it.
3. **Establish whether Zeebra's F4 does asymptotically more work than a comparand on the same
   ideal.** This is one cheap measurement and it determines whether any data-structure work can
   reach parity.
4. *An objective on the Fukuoka challenge import path was moved out with the cryptanalysis research
   in #668; it is preserved at commit 9532a9a2.*
5. **Extend the competitive corpus to a second reference field and a second comparison task**, so
   the board measures more than one prime and more than one objective.
6. **Take one algorithmic decision on evidence** — one bounded prototype, or an explicit record that
   no candidate is yet justified.

## 3. Scope, and explicit non-goals

In scope: the `normal_form` reduction loop and final interreduction; the Fukuoka importer, answer
parser, generator, field representation and differential oracle; the competitive corpus's fields,
rungs and tasks; one algorithmic prototype chosen by gate; and the measurement discipline that lets
any of it be believed.

**Not in scope, each for a recorded reason:**

| excluded | reason |
|---|---|
| **FGLM / order conversion (#58, #224, #368)** | M26-B's stage-1 characterization is not on record, so there is nothing to build on; and #323 measured F4 refusing before FGLM was reached at Anemoi `N = 6`. Conversion is a **parity** objective and M27 has two better-evidenced ones. Carried, not cancelled |
| **Signature-based F5 (#223)** | **A complete won't-do, resolved negatively 2026-11-06.** 33–60% of F4's pair rows add no rank, bounding the direction at ~2x; F4 and F5 compute the same reduced basis so the max degree is a property of the ideal; and F5's author records "bad performance is expected when the system is overconstrained" against Zeebra's `m = 2n` targets. Nothing is left open |
| **A mutant mode (#74's MF4 half)** | M22-D measured it: **0, 1 or 2 degree regressions per computation**, every one already following a mutant, because `PairQueue::select_batch` takes the lowest pending degree. The benefit is already captured by degree-first selection. MF4 proper is a different algorithm and sits in the family M22-C measured at **214x slower** |
| **Hilbert deferral** | M22-C measured and rejected it: 1.28x faster on one instance, **214x slower** on another, and it crosses the column budget on an instance the baseline finishes in 374 ms. The limiting variant is already shipped as selectable-not-default, and it is a *memory* strategy |
| **Wiedemann for F4 echelonization (#58)** | "It computes the wrong object." The output *is* the transformed matrix; the matrices are rectangular and deliberately rank-deficient, and the rank defect is the answer. **Do not reopen for F4.** This does not bear on XL, where a linear system genuinely is solved — §5.5 |
| **Elimination-kernel specialization (#269)** | Rule 2. 13.9% on `mq-random-10`, ceiling 1.16x |
| **Bit-packed GF(2) / GF(2^e) linear algebra (#272)** | Real and well-sized — one bit of information occupies 16 bytes, and the kernel is fully generic with no char-2 path. But **Zeebra's importable Fukuoka types are III and VI, both GF(31)**, so it does not help the frontier this milestone targets. The GF(2) types are not importable. Carried as the first M28 candidate |
| **GPU and out-of-core (#69, #86–#89, #225)** | No named kernel, workload, predicted benefit or benchmark. Unchanged from M26 |
| **Griffin/FreeLunch (#202, #306)** | Buys one family. Deferred, not rejected |

*Two rows on further Poseidon round counts and their cost projections were moved out with the
cryptanalysis research in #668; they are preserved at commit 9532a9a2.*

---

## 4. Issue reconciliation

### 4.1 Carried into M27 as written

| issue | workstream | why it carries |
|---|---|---|
| #447 | **M27-A, gate 0** | The 348x against Groebner.jl, and the screen showing no stage explains it. Its first deliverable — pair, batch and matrix counts for both engines on one digest — decides whether M27-A can reach parity at all |
| #440 | M27-A | `normal_form` rebuilds the whole dividend every step: Θ(R·W) in both copies and comparisons. Three stages, and its own comment inserts the cheap one ahead of the heap |
| #436 | M27-A | The 99.94% split, and candidates 1–3 that #440 does not attack |
| #268 | M27-A / M27-B | Carried **re-scoped**, not reinstated: its own latest comment narrows the 4.9% ruling to what it measured and proposes finding the 20-variable crossover on `fukuoka-mq-III-n20-seed0` — M27-B's instance. §1.3 |
| #331 | M27-A | A monomial divmask for the reducer search — scoped to symbolic preprocessing, and #436 candidate 1 is the same question inside `normal_form` |
| #317 | M27-A | The packed monomial with a cached total degree, gated on a `cmp` microbenchmark. §1.3's reopening lands here |
| #322 | **M27-B, prerequisite** | The effective entry limit is `min(max_live_nonzeros, max_live_bytes / 16)` — confirmed at `options.rs:400-412`. **Raising one knob to re-reach III n=20 does nothing**; this is what must land first |
| #414 | M27-B | The real GF(2^8) header does not parse and the coefficients are hex. **Two coupled changes**, see §5.3 |
| #415 | M27-B | `parse_answer` has no error channel at all, so a hex answer yields nine wrong coordinates silently |
| #421 | M27-B | A `Gf256Mq` arm in the oracle dispatch. **Not a one-line change**, see §5.3 |
| #420 | M27-B | Generate from `(type, n, seed)` rather than retaining bytes. Achievable exactly for types I–III |
| #70, #197 | M27-B | The Fukuoka parents. **#70 closed 2026-11-08**: its F4 baseline is recorded in fukuoka-mq.md §4 (moved out in #668) — 111 ms on the published type III `n = 10`, `D = 1`, the published answer recovered — and the "deferred" note described the M26 freeze window, not the state. #197 is its successor and names #414/#415 as blockers of its GF(2^8) half, both since merged |
| #425 | **M27-C, first** | `text_instance` labels an instance with a characteristic it did not generate over. Blocks #426, and affects **three** constructors, not the two the issue names — §5.4 |
| #426 | M27-C | GF(32003). Larger than it looks: it is what makes msolve an **eliminant** comparand for the first time — §5.4 |
| #424 | M27-C | Extend the Katsura and Cyclic ladders to the published rungs |
| #427 | M27-C | GF(2) Cyclic rows |
| #428 | M27-C | A floor-free comparison statistic. The board holds stage times in `history.json` and renders them as free text; no stage-based ratio exists anywhere in `board.rs` |
| #429 | M27-C | Homogenized Cyclic. Closes if #424 reaches `cyclic-7`/`cyclic-8` affine |
| #332, #341, #385, #386, #446 | M27-C | Five recorded board defects, each small and each affecting what may be published |
| #439, #441 | M27-C | The Magma studies. **Invariants, within-implementation ratios and difficulty scales only** — `classical-benchmarks.md:160` forbids any wall-clock comparison against a 2004 figure, and Magma is not installed here |
| #256 | M27-C | The competitive research parent |
| #76 | M27-D | XL with block Wiedemann — and it is the **published record-holder for types II and III**, which is M27-B's family. Currently Low; §5.5 raises it |
| #74 | M27-D | Hilbert-driven F4. Its *deferring* half is ruled out, but the scale question is open: HDF4 holds the type VI record at `m = 24` where Zeebra measured it non-winning at `n = 10` |
| #273 | M27-D | Adaptive strategy selection. `src/grobner/planning/` exists; exactly one of its decisions rests on a measured quantity |
| #442 | M27-D | The per-step degree sequence. Accurate as written — aggregates exist, the sequence does not, and the push site is `mod.rs:356` where the batch degree is computed and discarded |
| #318, #319 | M27-0 | Rule 3. Unresolved, and they bound every ratio M27 quotes |
| #334, #335 | M27-0 / M27-I | Cost-model rows emitted by runs rather than transcribed; and no measurement in `docs/research/` records its commit |
| #410 | M27-0 | `RowCost::of` models the determinant term only — the 15% — and ignores the 73% symbolic build. A guard that admits a row by modelling the term that is no longer dominant |
| #412 | M27-0 | The recorded **3.21x** width penalty is a ratio of two *pairs*, not of two widths. Swept in one process the Euclidean kernel is **1.100x at 32 workers, 90.9% efficiency** over the row's own pair — lower than the dense kernel's 1.178x at 8 workers in the same session. The gap was a missing specialization term in `euclidean_core_ms`, 2.00x the remainder sequence it feeds; the allocator candidate is refuted |

### 4.2 New issues

| issue | workstream | why it did not exist |
|---|---|---|
| **#450** | — | The milestone epic |
| **#451** | M27-0 | Nothing tracks reconciling M26's landed work into a quotable baseline, and the `rf4-rp2` row has **three** mutually inconsistent cost tables — §5.1 |
| **#452** | M27-A | `benches/f4_stages.rs:23` states that interreduction is outside every stage; `StageTimings` has a single `interreduction: Duration`; and #436's 99.94% exists only in a commit message. The headline figure of M27-A's workstream **cannot be reproduced from the tree** |
| **#453** | M27-B | The retained record predates #305 and #437, and `f4-resource-scaling.md` §10.4 explicitly declines to answer what now binds. No issue asks |
| **#454** | M27-B | `SUPPORTED_DIMENSIONS` is `[10, 15, 20]` — the toy sizes. The smallest *real* importable challenge is type VI m=16 → n=24, so no challenge instance can be imported at all |
| **#456** | M27-C | `one-finite-field-solution` is refused by **all four** comparands, verified per engine from source. The second task has to be `univariate-eliminant`, which needs a field below msolve's eliminant ceiling — §5.4 |
| **#457** | M27-D | #74, #76, #272 and #273 are candidates; #77 owns the metric; nothing owns *choosing between them and recording the refusal* |
| **#471** | M27-A | #447's answer named it and §6 of the Groebner.jl study never proposed it: the stage needs replacing, not speeding up |
| **#458** | M27-I | The integration-and-report role, mirroring #299 and #370 |

Thirty-six issues are attached as sub-issues of #450. **Eight are not, and the reason is mechanical
rather than a scope judgement:** GitHub permits an issue only one parent, and #318, #319, #268, #322
and #256 are already sub-issues of #371 (M26), #70 of #65, and #74 and #76 of #66. Those carry their
M27 scope by the `M27` label and by this document, and M26's treatment of #297 is the precedent.

**Priorities set or changed during planning**, each with a comment on the issue recording why:
#450, #451, #452, #453, #458 **High** (new); #436 **High** (previously unset — it is the issue the
5.10x ceiling belongs to); #426 **Medium → High** (two deliverables sit behind it); #415
**Medium → High** (the silent-failure half of the GF(2^8) chain); #454, #456, #457 **Medium** (new);
#76 **Low → Medium** (to a narrower question than its body implies — §5.5); #268 **Low → Medium**
(re-scoped to the 20-variable crossover, not reinstated — §1.3).

### 4.3 Deferred, with the reason

#58 / #224 / #368 (FGLM — M26-B's characterization is not on record); #223 (a complete won't-do);
#272 (right-sized, wrong field for this milestone's targets); #202 / #306 (one family); #262 (Rule 2
still, and #349 implicated interreduction rather than elimination); #218–#221 (formulation work
first); #269 (Rule 2); #69, #86–#89, #225 (no named workload); #198, #201, #203, #204, #206, #207,
#219, #220 (each a research issue with no credible smallest target yet; #206's own document declines
to register anything and recommends challenge C's *shape* as the first step).

**Two housekeeping observations made during reconciliation, neither scheduled here.** #223 is
**ready to close as a won't-do** — its own final comment says so, and §3 records the three legs. And
**#274 is closed while its deliverable is unmerged**: `docs/research/external-provenance-policy.md`,
695 lines, exists on branch `docs/274-provenance-policy` (`77b97c2`) with **no PR opened**. M27
relies on that policy in §5.3 for the Fukuoka "no grant" class, so whoever opens that PR should know
M27 cites it. Both are M27-I's to raise, not M27's to do.

*A paragraph on an attack reward programme was moved out with the cryptanalysis research in #668; it
is preserved at commit 9532a9a2.*

### 4.4 Shared code areas that make concurrent implementation unsafe

M25 named `src/grobner/f4/`, `src/linalg/` and `src/fields/`. M27 corrects one of those and adds
two:

- **`src/poly/multivariate/sparse_multivariate_polynomial_arithmetic.rs`** — `normal_form`,
  `Reducer`, `sorted_terms`, `subtract_shifted`. **M27-A only.** The single most contended file in
  this milestone.
- **`src/grobner/buchberger.rs`** — and this is the correction: **final interreduction is not in
  `src/grobner/f4/`.** `reduce_grobner_basis_until` is at `buchberger.rs:286` and the 80.4% loop at
  `:322-343`. **M27-A only.** It also holds the `interreduction_naive` differential oracle at
  `:1283`.
- **The monomial type** — `monomial.rs`, `monomial_arithmetic.rs`, `monomial_order.rs`. **53 files
  mention `exponents`**; heaviest are `multi_poly_parser.rs` (46 sites),
  `sparse_multivariate_polynomial_arithmetic.rs` (42), `f4/symbolic.rs` (30),
  `sparse_multivariate_polynomial.rs` (28), `monomial_order.rs` (27). **Sequenced, never
  parallelized**, and inside M27-A's checkout.
- **`src/grobner/f4/options.rs` and `statistics.rs`** — wanted by M27-A (new sub-stage timings, any
  new strategy knob) **and** M27-B (#322's budget coupling, resource reporting). These are the one
  genuine cross-workstream overlap; §8 assigns them.
- **`src/grobner/external/corpus.rs`** — **M27-C only.** It carries 19 frozen digests.

One further hazard that is not a file: **`normal_form`'s divisor-selection order is observable.**
FGLM border normal forms are pinned in `src/grobner/differential/fixtures.rs` and checked by
`differential/mod.rs:738-820`, and the documentation at `:330-333` states that the result depends on
divisor order. Reordering reducers is a behaviour change, not an optimization. #440's acceptance
criterion — a bit-identical reduced basis — does not by itself protect these fixtures.

---

## 5. Workstreams and technical specifications

### 5.1 M27-0 — the baseline nobody can currently quote

**Issues:** #451, #318, #319, #410, #412, #334, #335.
**Depends on:** #370 and #435 for completeness; starts without them.

The deliverable is one document under `docs/research/` that a later agent can cite instead of
re-deriving. It must record, each with its commit, `ZEEBRA_MACHINE`, `ZEEBRA_AFFINITY` and basis
label:

1. **`mq-random-10`'s stage split re-measured at the current commit.** The *ratio* no longer needs
   reconciling — #435 re-took both sides on one cohort, so the board publishes **4.13x** at `663097a`
   (28.71 s / 6.96 s) and **4.14x** at `7adb29e` (29.01 s / 7.00 s), each self-consistent, and the
   append-only history keeps both. What is *not* re-taken is **#349's 80.4% stage split**, which
   dates from before #304/#437 removed two copies of the basis from the stage it measures. The
   Amdahl ceiling M27-A's entire target rests on is therefore inherited rather than current, and
   this is the measurement that fixes it. Until then, 80.4% and 5.10x are carried as **pre-#437**
   figures and labelled so.
2. *An item on the cryptanalysis frontier by class was moved out with the cryptanalysis research in
   #668; it is preserved at commit 9532a9a2.*
3. *An item reconciling the `rf4-rp2` Poseidon row's cost tables was moved out with the
   cryptanalysis research in #668; it is preserved at commit 9532a9a2.*
4. **Each selected target's barrier**, by stage reached and the actual reason for stopping. Runtime
   alone is not an indicator of progress toward a solution.
5. **The competitive baseline per engine**, now that #435 has merged: the `7adb29e` cohort's walls
   and the board's published ratios, with Sagebrush marked non-authoritative, Groebner.jl's
   inner-time-versus-process-wall gap stated, and the 53 `unsupported` and 14 `stopped-by-limit`
   rows counted rather than dropped.

**#410 is a safety fix and lands here**, not in a Poseidon workstream: a guard that models the 15%
and ignores the 73% is a guard waiting to admit a row nobody costed. **#412's falsification does not survive its own
mechanism**: the 3.21x was a pair ratio with a 1.100x width penalty folded into it, so §5.2's
prediction that axis 4 would not contend worse was right and the one-term cost law was what was
wrong (`structured-sylvester.md` §5.6.2).

### 5.2 M27-A — the `normal_form` loop, and the question of how much work Zeebra does

**Issues:** #447 (**answered** — `docs/research/groebner-jl-gap.md`), #452 (the instrumentation it all
rests on), **#471's matrix interreduction (factor B, 5.03x)**, #317 (factor C, 14.0x), #440, #436,
#331, #268.
**Primary files:** `src/poly/multivariate/sparse_multivariate_polynomial_arithmetic.rs`,
`src/grobner/buchberger.rs`, the monomial type, `benches/sparse_polynomial.rs`.

**Gate 0, and it comes before everything — #447.** Pair, batch and matrix counts for Zeebra and for
a comparand on `mq-random-10` grevlex at the same digest. Both engines can report them. The question
is whether Zeebra reaches a *different number of matrices, pairs or batches* on the same ideal.

> **If Zeebra is doing asymptotically more work, no data-structure change closes the gap**, and
> M27-A's ceiling is the Singular gap alone. That is still worth 2x, and the plan says so in
> advance so the result cannot be re-interpreted after the fact.

Settling whether Julia's JIT lands inside Groebner.jl's timer belongs here too, and is arguably
second after the counts.

**Then #440's three stages, separated by what each attacks.**

*Stage 1 — instrument.* On `mq-random-10` at the recorded digest: terms copied by
`subtract_shifted`, `order.cmp` calls, monomial multiplies at `:491`, reducer-scan steps at `:348`,
and mean and max `working.len()` per step. **Critically, the per-step split between the comparison
region `[0, pos(q·tail_max)]` and the memcpy region above it** — they cost wildly different amounts
per element and the ratio decides stages 2 and 3. Four verdicts, not three: **compare-bound,
copy-bound, search-bound, or none of them.** If `W` is small, nothing below can pay and the issue
closes cheaply. That is a complete result.

*Stage 2 — window the merge.* Both sequences are sorted ascending, so the merge starts at
`working`'s smallest term and pays comparisons over terms the tail never touches.
`partition_point` for the smallest shifted tail term, memcpy below it, merge only the straddled
span. Removes the Θ(R·W) in comparisons and monomial multiplies; keeps it in term copies.
Correctness is **total rather than probabilistic** — no tail term maps below `shifted_min`, so
region 1 cannot cancel, and the cancellation check only fires on `Ordering::Equal`. Downside bounded
at one binary search per step.

*Stage 3 — heap division* (Monagan–Pearce), behind a `ReductionStrategy`, **only if stage 2 leaves
the copies dominant.** Θ(R·log k) for k active divisor-tail streams. Large, cache-hostile, and it
replaces a sequential memcpy that is close to memory bandwidth with random access.

> **Stage 2 landing and stage 3 being refused on its numbers is a success**, and the issue closes
> that way without stage 3 being written.

**#436's candidates 1–3 are orthogonal and stay #436's**: the reducer search (`find_map` at `:348`,
linear in up to 246 reducers, rebuilt per call); no caching between element `i` and `i+1`; and the
`O(n²)` shape itself. `F4Statistics` already reports **16.6 divisor scan steps per query** on this
instance — but only for the batch path, so whether interreduction behaves similarly is unmeasured.

**#317 carries §1.3's reopening.** If stage 1 returns *compare-bound*, the monomial representation
is implicated inside the 80.4% stage, which #268's 4.9% screen never covered. Gated on stage 1, and
gated again on the `cmp` microbenchmark #317 already asks for, because `Monomial` is serialized.

**The infrastructure gap is a deliverable in its own right.** There is no interreduction benchmark;
`StageTimings` cannot split the stage; and the 99.94% figure is unreproducible from the tree. That
must be fixed before any A/B, or M27-A's headline is a number nobody can re-derive.

**Correctness requirements.** A bit-identical reduced basis on the correctness corpus — a reduced
Gröbner basis is unique, so this is exact equality and not a tolerance, and no change here touches a
non-exact operation. Differential agreement against `interreduction_naive`. The FGLM border
fixtures asserted unchanged, per §4.4. The existing route retained and selected until the A/B is on
record. **The `mq-random-10` stage share re-measured against 80.4%, not a microbenchmark** — a
microbenchmark cannot see the thing being claimed, which is a share of a stage.

**Target: 2x end to end on `mq-random-10`**, against an M27-0 baseline, bit-identical output.
Exhausting the 5.10x ceiling would put Zeebra ahead of Singular and still 17x–68x behind the other
three; the plan states that now so no report can imply otherwise.

A separate question is noted and **not** scheduled: whether solution-oriented workflows can skip
final reduced-basis construction. It is attractive precisely because the stage is 80.4%, and it is
excluded because such a route is not task-equivalent to computing a reduced basis and must never be
compared as though it were. It is an M28 candidate with a protocol prerequisite.

### 5.2a M27-A's first item — final interreduction as one Macaulay matrix (#471)

**This is the largest implementable lever in the repository, and #447 is what found it.** It is not
in §6 of the Groebner.jl study, because §6 was looking for stages to speed up and this stage needs
*replacing*.

**What Groebner.jl does** (`src/f4/f4.jl:106-171`, `f4_autoreduce!`): `matrix_reinitialize!` to
`basis.n_nonredundant` rows; each non-redundant basis element becomes an **upper row** at multiplier
1; `f4_symbolic_preprocessing!` supplies the reducers those rows need; **every** column is marked
`UNKNOWN_PIVOT_COLUMN` so all of them are eliminated against rather than treated as already reduced;
`linalg_autoreduce!`; `matrix_convert_rows_to_basis_elements!`; then the leading-monomial
divisibility sweep that drops subsumed elements. One matrix, the same hashtable, the same sparse
kernels as every other batch. Measured: **250 x 604, 1.74 ms, 2.0% of `f4!`.**

**What Zeebra does** (`src/grobner/buchberger.rs:287-352`): `minimize_grobner_basis`, sort ascending
by leading monomial, then for each of the 247 elements in turn `p.normal_form(&others, order)`,
writing each remainder back in place. `normal_form` pops the working polynomial's leading term,
**linearly scans all 246 reducers calling `checked_div`**, and `subtract_shifted` merges the chosen
tail back. **247 sequential divisions, each with its own intermediate growth.**

24 136 ms over 247 elements is **97.7 ms per element**, against a final basis whose entire monomial
support is **604 monomials**. That is intermediate expression swell — precisely what F4's matrix
formulation exists to avoid, and which Zeebra avoids everywhere in F4's main loop and then pays once,
at the end, for four fifths of the run.

**Zeebra already owns every component.** `src/grobner/f4/macaulay.rs` builds Macaulay matrices,
`src/grobner/f4/symbolic.rs` finds reducers, `src/linalg` eliminates them, and
`minimize_grobner_basis` already produces the row set. **What is missing is the assembly.**

**The correctness argument is already written in the tree**, at `buchberger.rs:306-314`: a reduced
Gröbner basis is determined by its leading monomials, so the route to it cannot change the answer.
That makes the acceptance criterion exact equality rather than a tolerance.

### 5.2a.1 **Delivered**, and the estimate was wrong in an instructive direction

**#471 landed and measured 4.18x end to end** (PR #478, `docs/research/interreduction-cost.md` §3a):
three reps interleaved in one process on one build, on the lock, with both routes' bases asserted
**equal** on every run.

| | division | matrix | ratio |
|---|---:|---:|---:|
| total (median of 3) | 40 809 ms | **9 753 ms** | **4.18x** |
| the stage | 35 247 ms | **4 094 ms** | **8.59x** |
| stage share | 86.4% | 42.1% | — |

Run-to-run spread is 1.009x and 1.030x, so the result is two orders of magnitude outside the noise.
**This clears §10's Strong criterion of 2x end-to-end with a bit-identical basis.**

**The estimate above said ~170 ms for the matrix pass. It measured 4 094 ms — 24x out.** The error is
not in the per-operation constant; it is in the *shape*. Groebner.jl's autoreduce matrix is
250 x 604; Zeebra's is **7 642 x 7 996**, which is **405x the cells**. 405x cells against 24x time
means Zeebra's per-cell cost is *better* than the scaling assumed — the pass is slow because the
matrix is enormous.

And 250 rows for 247 elements says Groebner.jl's closure added about **three** reducer multiples
against Zeebra's **7 395**, with its 604 columns being almost exactly `247 leading + 354 standard
= 601` — so **nothing in its tails is reducible at all**. That is a property of the main loop:
Groebner.jl reduces rows fully against pivots in every batch, Zeebra extracts candidates from an
echelon form that was never back-substituted, so each batch leaves reducible tails and the debt
accrues to the end. **#477** owns not accruing it, with Groebner.jl's 1.74 ms as its ceiling.

**The lesson for the rest of M27**, and it is §9's rule arriving from a new direction: a
stage-level estimate built from a comparand's cost is only as good as the assumption that both
engines build the *same object*. They did not. The ceiling was right; the cost model under it was
not.

**The division route is retained, not replaced.** `normal_form` is on the critical path of FGLM
border reduction, the differential oracles and `multi_div_rem`; and its divisor-selection order is
observable through the pinned border fixtures (§4.4). The matrix route is selected for *final
interreduction* behind an explicit option, with the division route as the fallback and as the
differential oracle for the new one.

---

### 5.3 M27-B — the Fukuoka frontier, and the GF(2^8) path

*This workstream (the Fukuoka challenge frontier and its import path) was moved out with the
cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

### 5.4 M27-C — a second field, a second task, and the corpus defects

**Issues:** #425 (first, in flight as PR #455), #426, #456 (the second task), #424, #428, #427,
#429, #332, #341, #385, #386, #446, #256, #439, #441.
**Primary files:** `src/grobner/external/`, `examples/competitive_sweep.rs`,
`research/competitive/`.

**#425 lands first, is larger than it is written, and is already in flight.** `text_instance`
renders generators from `type Reference = PrimeFieldElement64<REFERENCE_CHARACTERISTIC>` and then
labels them with the `characteristic` *argument*, which is never used for generation. The issue names
`katsura` and `cyclic`; **`planted_mq_instance` has the same defect**, so three of the four generated
families are affected. `random_mq_instance` is correct — it threads `CaseField::prime(characteristic)`
through.

**And the issue's own "latent" framing is wrong, which PR #455 establishes.** `msolve.rs`'s eliminant
tests already ask the corpus for rungs at `P30 = 1 073 741 827` — a prime *below* msolve's eliminant
ceiling — and were being handed systems reduced mod 2^31−1 and labelled mod 2^30+3. Those two tests
are what caught it. So the defect was active, not dormant; what is true is that **no retained board
row is wrong**, because every stored row is at the reference prime. #426 remains unimplementable
until this lands, since passing `32003` today yields residues mod 2^31−1 declared as mod 32003.

**#426 is the keystone, and the reason is the second comparison task.** The brief for this milestone
asks for two comparison tasks: an equivalent reduced Gröbner basis, and one independently verified
solution. **The second is not available as a cross-engine comparison and will not become
available** — `one-finite-field-solution` and `all-finite-field-solutions` are refused by msolve,
Singular, Groebner.jl and Sagebrush at every field size, verified per engine from source. Scheduling
that comparison would be scheduling an empty column.

What *is* available as a genuine second objective is **`univariate-eliminant`**, which Singular and
msolve both support. msolve's eliminant ceiling is `p < 1 515 531 529` — a **second** ceiling,
distinct from its basis ceiling of 2^31 — and the corpus's reference prime of 2^31−1 is *above* it,
so the sweep correctly refuses to ask and **all 18 conversion rows are `unsupported` for msolve.**
That is also why **#369's own acceptance item 2 is unmet**: the repository's largest measured deficit
cannot currently be reproduced as a record.

So the corpus needs **a reference field below that ceiling**, and `32003` is #426's choice because it
is the prime the external timing tables are written in. (The test path already reaches a sub-ceiling
prime via `P30`, so the mechanism exists; what is missing is a *corpus* field, the identity decision
that comes with it, and swept rows.) Above the ceiling msolve does not merely refuse: sparse-FGLM
returns `NULL`, which is laundered into the genericity signal and into a `goto restart` loop with no
exit — measured at 25 353 retries and 1.37 M lines in 8 s, never exiting. So the field choice is not
cosmetic.

Zeebra's own solution route remains measurable against **itself and against a verified witness**,
and that is reported as a capability rather than as a ratio.

**The corpus's other axes, in dependency order.** #424 (Katsura/Cyclic rungs to the published sizes
— note `katsura-7` already refuses direct-lex F4 at 20 003 295 nonzeros, and the available
equivalence kinds for new rungs are `LiveOracle` or `KnownSolution`, since msolve ships only
`kat6-31.ms` and `cyclic5-16.ms`); #427 (GF(2) Cyclic, with field equations' inclusion stated
explicitly either way, since Steel's figures do not include them); #429 (closes if #424 reaches
`cyclic-7`/`cyclic-8` affine).

**#424 and #428 are alternatives on the same problem and must be sequenced, not both assumed.**
Both exist because the classical families sit on Singular's and msolve's startup floors. #424 makes
them legible by **making the instances bigger**; #428 makes them legible by **measuring an
engine-internal time instead of a process wall**. #369's rows change the balance: Groebner.jl
already reports an engine-internal time and so has no process floor, which makes `katsura-7` (15.9x)
and `cyclic-6` (6.2x) decisive *today* against that one comparand — and #424's own comment observes
that "at `katsura-9` every comparand becomes legible at once". So **#424 first**; #428's residual
value is then specifically **msolve and Sagebrush**, the comparands bigger rungs would still leave
on their floors, and it is scoped to that. #428 does not relax the floor guard and is never
substituted into the wall-clock ratio: the stage times are already stored in `history.json` and
rendered as free text, and **no stage-based ratio exists anywhere in `board.rs`** — it is a new,
separately named column with its own refusal conditions, including a refusal when stage resolution
is coarse relative to the figure (Singular reports whole milliseconds, so `katsura-4`'s stage reads
`0.0 ms`).

**Every added instance must have its mathematical definition and field representation validated
before a timing is published** — the invariant gate, and `Invariants::overlap()` consulted as well
as `agree()`, because an empty disagreement list over an empty overlap is not a verification.

**The startup floor is preserved exactly as implemented**, and it is not weakened to fill the board:
`FLOOR_MULTIPLE_REQUIRED = 2.0`, applied to the **minimum over both operands**, with a floor defined
as the shortest wall that library recorded and requiring `ROWS_FOR_A_FLOOR = 4` answered rows first.
Disqualified rows are kept and marked, never dropped. Measured floor: **35.91 ms** for Singular,
which removes 21 of 28 answered pairs, all 21 reading as Zeebra wins up to 501x. Groebner.jl, which
reports an engine-internal time, has no process floor — which is exactly why it makes the classical
families decisive and why #428 matters less for it than for msolve and Singular.

**Magma.** Not installed and commercial. #439 and #441 are **source and literature studies**, and
their output is invariants, within-implementation ratios and difficulty scales. The rule is
absolute: *no wall-clock speedup against a 2004 figure may be reported anywhere in this repository*,
and the Anemoi precedent is why — an apparent 507x Zeebra advantage over published Magma was mostly
Magma's generic arithmetic at `p ≥ 2^32`, the same ratio being 124.6 at `p = 65537`.

### 5.5 M27-D — one algorithmic decision, taken on evidence

**Issues:** #457 (the gate), #76, #74, #273, #442. **Metric from:** #77.

Most of the candidate list is **already closed**, with measurements, and the gate's first job is to
not re-litigate them: F5/signature is a complete won't-do at a ~2x ceiling; a mutant mode is ruled
out at 0–2 regressions per run; Hilbert deferral is ruled out at 214x; Wiedemann-for-F4 computes the
wrong object. §3 carries each with its figure.

**What survives, and the evidence for each:**

1. **XL with block Wiedemann (#76).** The strongest external evidence in the set: it is the
   **published record-holder for types II and III** — Verbel's type II n=38 at 811 805 s, and
   Chou–Niederhagen–Yang's type III n=38 at 23.34 d with VmPeak 49.45 GB — and type III is exactly
   M27-B's family. #58's refusal does **not** apply: it rules out Wiedemann as a replacement for F4
   echelonization, where the output is the transformed matrix and the rank defect is the answer. In
   XL a linear system genuinely is solved, and #76's framing already says so.

   **But #76 has since read the scale, and it is sobering.** eprint 2026/2641 is the type III
   implementation, and at `n = 38` its matrix is **N = 45 379 620 columns — roughly 550x beyond
   Zeebra's largest matrix to date (81 800)**; the paper additionally presents `n = 38` over
   `F256` as an **estimate rather than a completed solve**. So XL is not a route to the published
   record on this machine, and the gate must not treat it as one. What it may be is a route to a
   *smaller* type III rung whose F4 matrix is the measured barrier — and #76's own note that
   "type III over GF(31) remains the instance this issue can actually experiment on today" is
   exactly M27-B's instance. Its go/no-go is obtainable **from construction alone, without a
   solver**: measure XL's matrix dimensions, nonzero count and storage against F4's peak on one
   real instance. Currently **Low** priority; the gate should raise it to that bounded question and
   no further.
2. **HDF4 at scale (#74's limiting half).** HDF4 plus MF4 holds the **type VI record at m = 24**
   (Sakata–Takagi, 994 320 s), while Zeebra measured the limiting variant as a *memory* strategy
   that matches rather than beats an untuned fixed cap at n=10 and n=15. Those are not in conflict;
   they are a scale question, and it is a real research question rather than a contradiction.
3. **Variable ordering.** M22-E measured `last-round-first` at **1.67x and 1.61x faster with 2.1x
   and 1.3x less peak memory** on identical mathematical systems — "notably more than *critical-pair*
   order, which M22-A measured at no runtime effect at all." It is the cheapest measured lever in
   the repository and **no issue owns it as an F4 default question.** The gate should consider it
   first precisely because it is cheap.
4. **Adaptive route selection (#273).** `src/grobner/planning/` exists at 1 759 lines with
   `solve_one_planned`, a 13-feature `SystemShape` extractor, and report plumbing. Of its decisions,
   **exactly one rests on a measured quantity** (the counted quotient dimension against the FGLM
   span budgets); the rest are a constant-contradiction check, a fixed conservative opening, and a
   resource-failure fallback. What is missing is an objective parameter and measured criteria — which
   makes "extend the existing planner" accurate.

**The gate, and it may legitimately return "none".** It does not invent its own metric: **#77 owns
the comparison methodology** for epic #66 — time and peak bytes to a *verified solution*, so an F4
baseline must include FGLM and `solve_one`, with per-algorithm secondary metrics marked
non-comparable. The gate consumes that and adds only the choosing. That methodology is now
> written out in [`docs/research/mq-comparison-methodology.md`](research/mq-comparison-methodology.md)
> (#77), including the baseline column it validates itself against.

1. Name one benchmark instance and its **measured** bottleneck — from M27-0 or M27-B step 1, not
   from a literature claim.
2. Characterize the candidate's mechanism and its applicability to that bottleneck, distinguishing
   **overdetermined encryption systems** (`m = 2n`, types I–III) from **underdetermined signature
   systems** (`n ≈ 1.5m`, types IV–VI). The published record holders differ by exactly this split —
   XL for II/III, modified F4 for V/VI — and that is the most interesting structural fact in the
   Fukuoka record.
3. Estimate the reduction in time or memory, labelled measured / fitted / predicted / extrapolated.
4. Compare implementation cost, expected benefit and research risk.
5. **Choose one bounded prototype, or record explicitly that no candidate is yet justified.**

A kernel speedup is not an end-to-end solver improvement, and the gate's output must be a testable
implementation hypothesis rather than a survey. **#442 lands here regardless of the gate's choice**:
the per-step degree sequence is the input #81 and #334 both lack, the aggregates already exist
(`degree_regressions`, `max_degree_drop`, `regressions_after_mutants`, `max_mutant_degree_gap`), and
the push site is `mod.rs:356`, where the batch degree is computed for a comparison and then
discarded.

### 5.6 M27-I — integration, scoreboards, and the report

**Issues:** #458, #334, #335.

Owns **this document** — no workstream agent edits it; research documentation is written
independently under `docs/research/` and integrated here. Owns benchmark contracts and the runner
interface so M27-A, M27-B, M27-C and M27-D do not race on them. Owns scoreboard and competitive
regeneration, and `README.md`'s Status list, which M25 recorded as the usual cross-session merge
conflict.

Required report sections: competitive position; cryptanalytic position by class; the computational
frontier against M26; end-to-end performance improvements; peak-memory changes; new capabilities;
**negative results and failed hypotheses, as deliverables rather than omissions**; cost-model
prediction accuracy; remaining barriers to the next larger instance; and an M28 recommendation in
§13.9's form — what to run first, why, and what it is contested by.

Every claimed improvement traceable to an executable benchmark and a retained record, with
`ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY`. Every §10 criterion scored explicitly, including the ones
not met. M25's report was willing to record **"not met — the opposite"** against its own stretch
criterion; that standard holds.

---

## 6. Research gates and go/no-go decisions

### 6.1 Gate M27-0 — nothing is quoted until it is re-derived

No M27 figure is published against an M26 figure until M27-0 records both with their commits. #318
and #319 resolve or are **explicitly bounded as a ~20% systematic** before any cross-boundary ratio
is quoted. The `rf4-rp2` row resolves to the retained record.

### 6.2 Gate M27-A — **answered**, and the answer reorders the workstream

The gate as written asked whether Zeebra does asymptotically more work. **#447 measured it and the
answer is no** — the counts agree to 0.6% on pairs and exactly on batches, matrices, basis
cardinality and quotient dimension. The branch that would have capped M27-A at the Singular gap is
dead, and the one that survives is "the counts agree and the per-step cost differs", with the cost
decomposed into factors B and C.

So the order is now:

| rank | item | ceiling | status |
|---|---|---:|---|
| 1 | **matrix-based final interreduction** (#471, §5.2a, factor B) | **5.03x** | **done — 4.18x end to end, PR #478.** It also exposed #477, which owns the stage's remaining 42% |
| 2 | **the monomial representation** at two words (#317, factor C) | *not a stage; the screen cannot bound it* | gated on #317's own `MonomialOrder::cmp` microbenchmark **before** touching the type, because `Monomial` is serialized and a new field is a format change. The `HashMap<Monomial<N>, F>` term store belongs in the same screen, and nothing has measured the two apart |
| 3 | #440's window-the-merge, #436's candidates 1–3, #331 | bounded by what remains of the division route after item 1 | these now serve FGLM border reduction, the differential oracles and `multi_div_rem` rather than F4's hot stage. Still worth taking, no longer the headline |
| — | #268 §6.1-style interning, divmask, delayed reduction | **1.014x–1.16x** on the losing column | won't-do, now on measured evidence rather than inference |

**#440's stage 1 is still worth running and its scope narrows to a loose end #447 named:** intermediate
swell in `normal_form` is **inferred, not measured** — nothing counts terms popped or `checked_div`
calls. Two counters settle it and distinguish swell (terms popped ≫ terms in the answer) from scan
cost. #452 adds them. The replacement is the same either way, which is why item 1 does not block on
it.

### 6.3 Gate M27-B — the diagnosis authorizes the run, not the other way round

*This gate (M27-B's Fukuoka run authorization) was moved out with the cryptanalysis research in
#668; it is preserved at commit 9532a9a2.*

### 6.4 Gate M27-C — #425 before #426 before the second task

#425 is a correctness fix and unconditional. #426 is unimplementable before it. The second
comparison task is unimplementable before #426, because msolve's eliminant ceiling sits below the
current reference prime. #424, #427, #428 and #429 are independent of that chain and of each other.

**The protocol is not weakened to fill the board.** Added records will add startup-floor
disqualifications; they are reported, never dropped. No ratio against a tool that could not accept
the input or that computed a different object. And the coverage assertion is run **locally** before
any merge touching the comparands, the corpus or the challenge registry, because CI has no msolve:

```sh
ZEEBRA_REQUIRE_MSOLVE=1 cargo nextest run --profile ci --lib -E 'test(/^grobner::external::/)'
```

### 6.5 Gate M27-D — "no candidate is justified" is a passing outcome

The gate's five steps in §5.5, with the instance and bottleneck taken from a measurement rather than
a claim. If no candidate clears it, the recorded refusal is the deliverable and M27-D closes
negative. **A literature survey is not an outcome**; a testable implementation hypothesis is.

---

## 7. Experimental baselines and methodology

### 7.1 Hardware, recorded because every figure depends on it

AMD Ryzen Threadripper PRO 5995WX, 64 cores / 128 threads, 1 socket, L3 256 MiB across 8 instances,
503 GB RAM. Fedora, Linux 7.2.10, gcc 16.2.1, rustc 1.99.1. No root. Measured figures record
`ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY`. Run-to-run noise band **~20%**; differences under it are not
read.

### 7.2 Protocol, inherited and not weakenable

- **Serialize benchmarks on the lock.** `tools/benchlock.sh <owner-tag> <command>`, plus per-agent
  target *and* scratch directories. A clobbered `tee` is a silently wrong figure. `end=exited`
  rather than `status=0` is what asserts completion. **A figure taken without the lock is not
  publishable.**
- **Timings on the lock; peaks may be taken off it.**
- **`tools/rss-guard.sh` for runs with material allocation risk.** Never find a measured binary with
  `pgrep -f` — a heredoc's own text is in its wrapper's cmdline. Exit 1 means **nothing was
  guarded, and that is not a pass**. Pass the pid from `$!` via `--kill-pid` when launcher and guard
  share a script.
- **Never `taskset … timeout … <binary>`.** `taskset` execs and keeps the pid; `timeout` forks and
  does not, which once produced a recorded instance wrong by ~7 000x. Pinning is applied to the
  harness process, which is inherited across `fork` and preserved across `exec`.
- **Build flags are verified, not assumed.** `RUSTFLAGS` *replaces* `target.*.rustflags`, so setting
  it for any reason silently drops the AVX2 floor; and a measurement crate outside the worktree does
  not inherit `.cargo/config.toml`. Verify with `cargo build -v 2>&1 | grep target-cpu`. This has
  cost this repository three sets of figures. Also `RUSTC_WRAPPER=""` and a private
  `CARGO_TARGET_DIR`, or an example compiles against a stale rlib.
- **Startup floor and task equivalence** on every cross-library row.
- **Peak allocated and peak resident are separate columns**, and an RSS figure on one basis may
  never be compared with one on another. The four bases are `DirectChildHighWater`,
  `ProcessTreeSampled`, `AllocatorTracked` and `Unavailable`.
- **`ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY` must be set or the records key wrong**, and `--all` is
  never passed to the scoreboard.

### 7.3 Stage-level attribution, and what it may be called

A stage share is a share. It may be called a ceiling under Amdahl and it may **never** be called a
speedup. **And per Rule 4, a ceiling is a ceiling against the comparand it was computed against.**
Any end-to-end claim is measured end to end.

### 7.4 Figure provenance

Every number is labelled **measured / fitted / predicted / extrapolated**; `Fitted` carries its
residual and its applicability limit; the cost-model register derives prediction error from the
predicted and measured columns rather than having it authored, and rows are append-only, so a
re-measurement sits beside the estimate it corrects instead of erasing how wrong it was.
A cryptanalytic witness is verified **through the primitive**, not only through the polynomial
system the solver generated.

---

## 8. Ownership and the parallel schedule

One writer per checkout, each on a real `git worktree` and its own branch.
`Agent(..., isolation: "worktree")` is not a reliable guarantee of file isolation for concurrent
writers.

| agent | worktree | branch | issues | primary files |
|---|---|---|---|---|
| **BASELINE** | `zb-m27-baseline` | `docs/m27-baseline` | #451, #318, #319, #410, #412 | `docs/research/` (new baseline note), `examples/resultant_cico.rs` and `research/cost-model/` (both moved out in #668) |
| **NORMALFORM** | `zb-m27-normalform` | `perf/m27-normal-form` | #452, #447, #440, #436, #331, #317 | `src/poly/multivariate/**`, `src/grobner/buchberger.rs`, `benches/sparse_polynomial.rs`, `benches/f4_stages.rs` |
| **FUKUOKA** | `zb-m27-fukuoka` | `feat/m27-fukuoka` | #322, #453, #414, #415, #421, #420, #454 | `src/grobner/research/mq.rs` and `examples/mq_challenge.rs` (both moved out in #668), `src/fields/`, `src/grobner/differential/**` |
| **CORPUS** | `zb-m27-corpus` | `feat/m27-corpus` | #425, #426, #456, #424, #428, #427, #429, #332, #341, #385, #386, #446 | `src/grobner/external/**`, `examples/competitive_sweep.rs`, `research/competitive/` |
| **RESEARCH** | `zb-m27-research` | `research/m27-algorithms` | #457, #74, #76, #273, #442, #439, #441 | `docs/research/` (new notes), `src/grobner/f4/mod.rs:356` for #442 only |
| integration | orchestrator checkout | — | #458, #334, #335 | **this document**, `README.md`, scoreboard and competitive regeneration, runner contracts |

### 8.1 The collisions, named

- **`src/grobner/f4/options.rs` and `src/grobner/f4/statistics.rs` are wanted by NORMALFORM (new
  sub-stage timings, any new strategy knob) and by FUKUOKA (#322's budget coupling).** This is the
  one genuine cross-workstream overlap. **FUKUOKA owns both files for the duration of #322**;
  NORMALFORM's instrumentation lands after #322 merges, or in a separate file under
  `statistics.rs`'s module with NORMALFORM owning only the new type. Sequence, do not merge
  concurrently.
- **The monomial type is sequenced inside NORMALFORM's checkout, never parallelized.** 53 files
  mention `exponents`. #317 is the last thing NORMALFORM does, if stage 1 funds it at all.
- **`src/grobner/external/corpus.rs` is CORPUS's alone.** It holds 19 frozen digests, and #425
  changes generation while #426 and #424 change the rung list.
- **RESEARCH writes documents, not source**, with the single exception of #442's push site at
  `mod.rs:356`. That one line is coordinated with FUKUOKA, which owns `f4/` during #322.
- **Benchmark measurements serialize on the lock across all five agents.** Parallel source
  development is desirable; simultaneous measurement is a silently wrong figure.
- After any parallel run, `git status` the orchestrator checkout and confirm no agent touched files
  outside its scope.

### 8.2 Claimed at the time of writing — do not re-assign without checking

`zb-claim.sh state` at `d9121c0`, and these move, so **re-check before picking anything up**:

| issue | state | who / what |
|---|---|---|
| **#447** | **live**, `agent:claimed` | M27-A's gate 0 is **already being worked**. NORMALFORM must `verify` before claiming it and should start from #440 stage 1 if it is still held |
| **#425** | **live**, `agent:claimed` | M27-C's first step is **already being worked**. CORPUS starts from #426's preparation and waits |
| #369 | live | `goofy-questing-lagoon@feat/369-populate-competitive-board` — this is PR #435. **M27 does not touch it** |
| #70 | **closed** | was `zb-r3-prov@docs/70-fukuoka-mq-provenance`, with "F4 baseline deferred (machine frozen for M26)". That lease went stale and the branch was never pushed; the baseline it deferred had meanwhile landed in fukuoka-mq.md §4 (moved out in #668), so #70 closed on evidence rather than being re-worked. FUKUOKA treated it as a parent, not as work |

A board-membership audit at `d9121c0` suggested several open issues were missing project rows.
**That reading was wrong, and the cause is now fixed:** #448 was `orient`'s open-issue read not
paginating past GraphQL's `first: 100` cap, which hid the twelve newest issues behind an `rc=0`
queue that looked complete — "succeeded, returned data, and was incomplete", a fourth outcome §0 of
`CLAUDE.md` was not written against. Fixed at `a062b59`. M27 schedules no board-repair work, and
M27-I confirms membership against the project directly rather than through `orient`.

### 8.3 Start order

**Immediately, in parallel, no measurement dependency:**

1. **CORPUS — #425** (already claimed; PR #455 open). A correctness fix, unconditional, and it
   blocks #426 and #456.
2. **FUKUOKA — #322**, then #414+#415 together, then #421. #452 waits on #322 releasing
   `f4/statistics.rs`.
3. **NORMALFORM — #447's counts**, which is gate 0 for the whole workstream and is cheap.
4. **BASELINE — #451's freeze document**, starting from what is on `main` and annotating what is
   not.
5. **RESEARCH — #439/#441's reads and the gate's candidate characterization**, which need no machine
   time.

**After one measurement each:**

6. **NORMALFORM — #440 stage 1**, then stage 2 or #436/#331 or nothing, per §6.2.
7. **FUKUOKA — #453's re-diagnosis**, after #322.
8. **CORPUS — #426**, after #425; then #456; then #424, and #428 scoped to what #424 leaves.

**Gated, and may legitimately never start:**

9. #440 stage 3 (heap division) — only if stage 2 leaves copies dominant.
10. #317 — only if stage 1 returns compare-bound.
11. A large Fukuoka run — only on a costed diagnosis and a recorded owner authorization.
12. M27-D's prototype — only if #457's gate clears a candidate.

**No longer blocked:** #435 merged at `25e10fe` during planning, so the five-library board is on
`main` and every workstream can read it. M27 still does not touch M26's PRs.

---

## 9. Resource budgets

- Ordinary benchmarks: short, modest, on the lock.
- Longer experiments require a documented cost estimate before launch, **including the dominant
  term** — #410 is the precedent for what goes wrong otherwise.
- **Any run projected to exceed ~2 h wall or ~64 GB peak RSS requires explicit owner
  authorization.** **The standing ceiling is not raised for M27.**
- Never an unbounded computation because a predictor suggests it might finish.
- An external watchdog even where an internal time budget exists.
- A run whose actual growth violates its approved ceiling is terminated.

**Authorized at the time of writing:** #447's pair/batch/matrix counts; #440 stage 1's
instrumented run on `mq-random-10`; the III n=20 re-diagnosis at current `main` (the old record
reached its stop in 67.5 s; the supervised re-run is budgeted at **≤ 30 min wall and ≤ 32 GB**, and
exceeding either terminates it); #426's and #424's corpus sweeps at their rung sizes; any
`competitive_sweep --measure` row at an existing rung.

*The list of challenge campaigns and round-count projections not authorized was moved out with the
cryptanalysis research in #668; it is preserved at commit 9532a9a2.*

---

## 10. Acceptance criteria

**Minimum.**

1. M27-0's baseline frozen with commits, affinity and machine.
2. ~~#447's work counts measured~~ — **met before implementation began** (`a1867a7`): the counts
   agree, the 344x decomposes into 4.89x / 5.03x / 14.0x, and the JIT question is settled at ~2%.
3. §5.2a's matrix interreduction landed with a bit-identical reduced basis and the stage share
   re-measured, **or** a recorded verdict naming what refused it; and #440 stage 1's counters on
   record settling whether `normal_form`'s cost is swell or scan.
4. *A criterion on the Fukuoka III n=20 barrier was moved out with the cryptanalysis research in
   #668; it is preserved at commit 9532a9a2.*
5. *A criterion on the Fukuoka GF(2^8) import path was moved out with the cryptanalysis research in
   #668; it is preserved at commit 9532a9a2.*
6. #425 fixed and #426 landed, so the corpus has a second reference field.
7. #428's floor-free statistic implemented, or a recorded refusal on its resolution.
8. #318/#319 resolved or explicitly bounded; the board and documentation truthful.

**Strong.** The minimum, plus:

- **At least 2x end to end on `mq-random-10`** against the M27-0 baseline, bit-identical reduced
  basis, with the stage share re-measured rather than a microbenchmark — **or** a recorded verdict
  naming the measured term that refuses it. §5.2a's estimate is **~5.0x**, which would land ahead of
  Singular on this row; 2x is the criterion because a ceiling bounds the conceivable, not the
  achievable.
- *A criterion on completing a published Fukuoka instance was moved out with the cryptanalysis
  research in #668; it is preserved at commit 9532a9a2.*
- A **measured narrowing of one competitive gap** on a workload clear of the startup floor, at
  task equivalence, with the invariants agreed.
- M27-D's gate taken: one bounded prototype chosen with its cost-benefit on record, **or** an
  explicit recorded refusal naming what would change it.

**Stretch.** At least one of:

- Competitive parity or a lead over an established system on a substantial workload under equivalent
  conditions, full correct computation, task-equivalent.
- An algorithmic advance that changes the practical resource-scaling behaviour on real MQ problems,
  demonstrated end to end.
- *Two criteria on cryptanalysis instances and published attacks were moved out with the
  cryptanalysis research in #668; they are preserved at commit 9532a9a2.*

**A kernel-level win alone does not satisfy the stretch criterion**, and neither does exhausting the
5.10x ceiling — that would put Zeebra ahead of Singular and still 17x–68x behind three other
engines. **The stretch criterion carries no numerical promise**, because the evidence cannot support
one: #447 shows the gap is not a stage, and until its work counts are measured nobody knows whether
parity is reachable by implementation at all.

---

## 11. What M27 will not claim

- That closing the interreduction gap closes the competitive gap. #447 decomposed the 344x and
  interreduction is **factor B of three**: removing it entirely leaves **4.89x** of randomized linear
  algebra Zeebra declines by policy and **14.0x** of per-operation constant, so ~70x is what items 1
  and 2 together could reach and **4.89x behind Groebner.jl's randomized figure is the floor** this
  milestone can aim at without changing its correctness regime.
- That an Amdahl ceiling computed against one comparand bounds the gap against another.
- That Groebner.jl's JIT explains the historical gap. #447 settled its variation at about 2%;
  comparisons still require matched task, invariants and timing regime.
- That a slice result is a result about the instance it was sliced from.
- That crossing a larger degree is nearer a solution.
- That a memory reduction is a frontier extension unless the resource stop actually moved.
- Any ratio against Magma's wall clock, at any date, on any instance.
- A ratio against a tool that could not accept the input, or that computed a different object.
- A ratio across the #318/#319 boundary without its ~20% systematic stated.
- A microbenchmark improvement reported as a share of a stage, or a stage share reported as a
  speedup.
- *Three non-claims about challenge instances, scoreboard classes and Poseidon round counts were
  moved out with the cryptanalysis research in #668; they are preserved at commit 9532a9a2.*

---

## 12. Risk register

| risk | likelihood | what it costs | mitigation |
|---|---|---|---|
| ~~PR #435 does not merge~~ — **resolved during planning** | — | — | #435 merged at `25e10fe`; the board holds 252 rows across five libraries and §1.1 reads from `main` |
| ~~Groebner.jl's 348x is a timer artefact~~ — **settled** | — | — | #447: three successive timed calls span **2.2%** and the sign inflates Groebner.jl. The board's 348x is also the conservative reading, since 9.33 ms of AbstractAlgebra conversion is inside `@solve_ns` and outside `f4!` |
| **The matrix interreduction pass costs more than the 170 ms estimated** | **moderate** | part of factor B's 5.03x | The estimate is Groebner.jl's 1.74 ms scaled by Zeebra's own 97.1x per-operation constant, which is the best-grounded stage estimate in the repository — but it is an estimate. The division route is retained, so a loss is recorded and reverted rather than shipped |
| **#440 stage 1 returns "none of them"** | moderate | M27-A's 2x target | That is a complete result and closes the issue cheaply. The 80.4% then needs #436's candidates 2–3 or an algorithmic answer, which routes to M27-D |
| **#447 shows Zeebra does asymptotically more work** | **moderate-to-high** | the parity half of M27-A, permanently | Stated in advance in §6.2 so it cannot be re-interpreted afterwards. It *strengthens* M27-D and hands it an instance |
| #317's monomial change has a 53-file blast radius | high if attempted | schedule, and merge conflicts across the repo | Last in NORMALFORM's sequence, gated twice, and never concurrent with anything |
| Two agents measure simultaneously | moderate | a silently wrong figure, the worst failure mode here | `tools/benchlock.sh` is mandatory and machine-wide; overlapping `START..END` windows are a machine-checkable proof the protocol was violated |
| The board is filled by weakening the floor | low | the credibility of every row | The floor is in code, not prose, and `is_publishable()` is the conjunction of both gates |
| **The milestone delivers only negative results** | moderate | the headline | Four of them would be genuinely valuable — #447's work-count answer, #440 stage 1's verdict, #453's barrier, and #457's refusal — and §10's Minimum is written so that all four count |

*Three risks on the Fukuoka frontier run and its import path were moved out with the cryptanalysis
research in #668; they are preserved at commit 9532a9a2.*

---

## 13. Deferred work and the M28 register

**Historical register at planning.** Conversion now ships, weighted orders exist, and challenge
instruments moved in #668. §15.6 scores these hypotheses and supplies the current recommendation.

| item | why not in M27 | what would schedule it |
|---|---|---|
| **Bit-packed GF(2)/GF(2^e) linear algebra (#272)** | Right-sized — one bit occupies 16 bytes and the kernel has no char-2 path — but Zeebra's importable Fukuoka types are GF(31) | A GF(2) or GF(2^8) workload that is actually importable, which #414 and the dimension ladder would create |
| FGLM / Krylov conversion (#58, #224, #368) | M26-B's characterization is not on record | That characterization, or a workload where conversion is the measured barrier |
| Solve without a final reduced basis | Not task-equivalent to a reduced-basis comparison | A protocol that can report it as its own task without conflation |
| Griffin/FreeLunch (#202, #306) | Buys one family | A generalization, or a witness it uniquely reaches |
| Boolean/SAT (#218–#221) | Formulation work first | A defined key-recovery workload and a comparison protocol that survives review |
| GPU / out-of-core (#69, #86–#89, #225) | No named kernel, workload, predicted benefit, benchmark | All four |
| Multigraded Hilbert series | `HilbertSeries` is single-graded — one numerator, one variable count, one degree argument — and `MonomialOrder` has three variants with no weighted or block order | #207 naming a workload that needs it |

*Four rows — MinRank, HFE, further Poseidon round counts and an attack reward programme — were moved
out with the cryptanalysis research in #668; they are preserved at commit 9532a9a2.*

**Initial M28 hypotheses, to test once M27's results exist:**

1. If #447 shows the work counts agree, then the remaining gap is per-step cost across *all* stages
   and the monomial representation is the single highest-leverage change in the repository —
   testable by #317's microbenchmark plus #440 stage 1's comparison region.
2. If the counts disagree, then pair handling and symbolic preprocessing set the gap, and HDF4 at
   scale (#74) and reduced Macaulay dimensions become the M28 program.
3. *A hypothesis on the Fukuoka III n=20 run was moved out with the cryptanalysis research in #668;
   it is preserved at commit 9532a9a2.*
4. *A hypothesis on XL against the Fukuoka III n=20 barrier was moved out with the cryptanalysis
   research in #668; it is preserved at commit 9532a9a2.*
5. Variable ordering at 1.6x–1.7x may be the best unclaimed lever in the repository, and an
   order-specific default is the shape M22-A's and M22-E's measurements jointly imply.

---

## 14. Reproducing

```bash
# the claim queue, before picking anything up
./scripts/agent/zb-claim.sh orient
./scripts/agent/zb-claim.sh id
./scripts/agent/zb-claim.sh token

# M27-0: what is on main, measured nowhere else
cargo run --release --example f4_profile -- mq          # the #349 split, digest-pinned
cargo run --release --example competitive               # render only; measures nothing

# M27-A gate 0 (#447) and stage 1 (#440). On the lock, pinned, flags verified not assumed
cargo build -v 2>&1 | grep target-cpu                   # must show x86-64-v3
RUSTC_WRAPPER="" ZEEBRA_MACHINE=workstation ZEEBRA_AFFINITY=0 \
  tools/benchlock.sh m27a taskset -c 0 \
  cargo run --release --example f4_profile -- mq
cargo bench --bench sparse_polynomial -- normal_form    # the microbench that cannot settle a stage

# M27-B's commands (the scoreboard, the MQ challenge fetcher and importer) moved out in #668

# M27-C: the competitive board. Measurement and rendering are separate binaries,
# and only --measure gives an attributable peak RSS
cargo run --release --example competitive_sweep -- --list
ZEEBRA_MACHINE=workstation ZEEBRA_AFFINITY=0-7 \
  tools/benchlock.sh m27c taskset -c 0-7 \
  cargo run --release --example competitive_sweep -- \
    --row katsura-6 --task reduced-grobner-basis --measure --wall 600 --write
. tools/external/env.sh                                 # msolve and Julia are not on PATH without it
ZEEBRA_REQUIRE_MSOLVE=1 cargo nextest run --profile ci --lib -E 'test(/^grobner::external::/)'

# M27-D's existing instruments
cargo run --release --example hilbert_study
cargo run --release --example hilbert_driven
cargo run --release --example f4_degrees
cargo run --release --example f4_schedule

# supervision for anything with allocation risk — never pgrep -f, and exit 1 is not a pass
tools/rss-guard.sh <comm> <id-substring> $((32 * 1024 * 1024)) --poll 10 --kill-pid "$!"

# the agent tooling's own tests
bash scripts/agent/test/zb-claim-test.sh
bash tools/test/rss-guard-test.sh
bash tools/test/benchlock-test.sh
```

`ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY` must be set or the records key wrong, and `--all` is never
passed. Commands are as of writing; `docs/guide/benchmarking.md` is authoritative for example
invocations.

### 14.1 Reproducibility checklist

Before any figure enters a report or a record:

- [ ] Taken under `tools/benchlock.sh`, with `end=exited` in the log.
- [ ] `ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY` set, and recorded in the record.
- [ ] `RUSTFLAGS` unset, `RUSTC_WRAPPER=""`, private `CARGO_TARGET_DIR`, and `target-cpu=x86-64-v3`
      verified by `cargo build -v`, not assumed.
- [ ] Commit recorded next to the figure, and the document's header declaration still true.
      `tools/check-measurement-provenance.sh` enforces the declaration's presence and runs in CI;
      what it cannot check is whether a *new* figure is inside the header's stated era, which is the
      author's to keep honest (#335, and `external-comparison-protocol.md` §10).
- [ ] Labelled measured / fitted / predicted / extrapolated; `Fitted` carrying residual and
      applicability limit.
- [ ] Peak allocated and peak resident in separate columns, each with its basis.
- [ ] For a cross-library row: same digest, same task, same limits, same machine, same affinity,
      both outcomes timing evidence, invariants agreed with a non-empty overlap, and the startup
      floor cleared by both operands.
- [ ] For a witness: verified **through the primitive**, and the class (`Official` /
      `FaithfulReduction` / `Engineering`) and formulation (including any slice and seed) recorded.
- [ ] For a resource stop: the resource named, the degree reached, the matrix dimensions, and the
      attribution of peak memory to a site — not just the budgeted quantity.
- [ ] If it touches the comparands, the corpus or the challenge registry: the coverage assertion run
      locally with `ZEEBRA_REQUIRE_MSOLVE=1`.
- [ ] Rebased onto current `origin/main` with CI re-run before merge, per the merge-staleness
      warning, which is advisory and does not block.

## 15. Integration report, 2026-11-11

**Evidence snapshot:** `ad175ffc`, including the certified scalar-Wiedemann converter, #456's
eliminant sweep and #678's groebner-rs comparand. **Measured at:** not measured here. This report
integrates the named measurements below and regenerates the competitive board from its retained
history; it takes no new timings, RSS samples or witness measurements. Historical §§0–14 describe
the planning state and intermediate decisions, not the current defaults.

**Verdict:** the **Minimum and Strong criteria retained in §10 after #668 are met**. The
competitive-lead alternative of Stretch is met on the named full reduced-basis workloads below;
it is not an all-engine lead. The other retained Stretch alternative, improved practical scaling
of a complete MQ solve, is **not established**. The broad representation, planner and Magma studies
remain open. Completing this report does not complete those studies or restore moved challenge
requirements to this repository.

### 15.1 Acceptance, criterion by criterion

| tier | criterion from §10 | result | deciding evidence |
|---|---|---|---|
| Minimum 1 | Baseline frozen with commits, machine and affinity | **met** | [M27 baseline](research/m27-baseline.md), frozen at `1985504`, re-verified at `53fbf50`; §2 names `ZEEBRA_MACHINE=workstation`, `ZEEBRA_AFFINITY=0-7`. Publication-bound historical figures and incomplete environment records remain qualified. |
| Minimum 2 | #447 work counts and JIT question settled | **met** | [Groebner.jl gap](research/groebner-jl-gap.md), `a1867a7`; matching batches, matrices, basis size and quotient dimension reject the extra-work explanation at that observation point. The approximately 2% JIT variation does not explain the gap. |
| Minimum 3 | Exact-basis matrix interreduction, stage share remeasured, and #440 counters | **met** | [Baseline §2.4](research/m27-baseline.md#24-the-interreduction-ab-at-53fbf50-and-it-comes-in-at-363x-rather-than-418x): exact basis equality, 3.63x complete basis computation, stage share 80.05% to 28.38%. [Interreduction §3](research/interreduction-cost.md#3-the-counts-and-the-verdict-rewrite-bound-not-swell-bound) records the copy-bound verdict; §§3g–3i adjudicate the other mechanisms. |
| Minimum 4–5 | Challenge barrier and GF(2^8) importer | **moved out of scope** | #668 moved these criteria and instruments; the prior tree is `9532a9a2`. No current-library claim is substituted for them. |
| Minimum 6 | Correct field generation and second reference field | **met** | #425/#426; `src/grobner/external/corpus.rs` generates and identifies `GF(32003)` separately. The retained history includes this characteristic, including #456's eliminant task. |
| Minimum 7 | #428 floor-free statistic or resolution-based refusal | **met** | `CompetitiveBoard::engine_internal_ratios` in `src/grobner/external/board.rs`; a separate engine-internal section, invariant/equivalence gates and a per-library resolution screen. It never replaces process-wall ratios. |
| Minimum 8 | #318/#319 resolved or bounded; truthful board and documentation | **met with disclosed historical limits** | [Resultant elimination §6.13](research/resultant-elimination.md#613-318-and-319-resolved-and-they-are-two-different-things) distinguishes quiet-box width effects from residual session drift. §15.2 retains failures, missing affinity and non-authoritative rows. This report updates current status without rewriting historical measurements. |
| Strong 1 | At least 2x complete MQ basis computation, exact output, stage share measured | **met** | The baseline's paired 3.63x A/B above clears the threshold without dividing different sessions. The later shipped-default cohort independently measures 5.86x (§15.3); these are different experiments. |
| Strong 2 | Complete a published Fukuoka instance | **moved out of scope** | #668; no witness or frontier completion is claimed here. |
| Strong 3 | Narrow a competitive gap above startup floor, equivalent task and agreed invariants | **met** | #575's `3d0e3759` reduced-basis cohort (§15.3), with checked invariants and process-wall comparisons against Singular. |
| Strong 4 | M27-D prototype selected or explicit justified refusal | **met by refusal** | [Algorithm decision](research/m27-algorithm-decision.md), reviewed at `800b75df`: defer an additional prototype; §5 names the bounded measurements that could reopen it. |
| Stretch 1 | Competitive parity or lead on a substantial complete task | **met on named workloads** | #575's complete reduced bases on `mq-random-10` and `katsura-11`, against Singular in the same cohort. Katsura's single attempts and load excursions limit its strength; the repeated MQ result stands independently. |
| Stretch 2 | Changed practical resource scaling end to end on real MQ solves | **not established** | Basis improvements and certified conversion measurements do not include complete point recovery and verification on such a solve. No kernel or conversion ratio fills that gap. |
| Stretch, moved alternatives | Challenge frontier or published attack | **moved out of scope** | #668; not scored as current-library achievements. |

### 15.2 Competitive position and board regeneration

Regenerate without measuring:

```sh
cargo run --release --example competitive -- --write
```

At the evidence snapshot, this reproduces the committed Markdown and JSON without changes. The
source is [`history.json`](../research/competitive/results/history.json); the rendered artifact is
[`COMPETITIVE.md`](../research/competitive/COMPETITIVE.md). There is no `scoreboard` example after
#668. #458's older command for that moved instrument does not apply to this checkout.

| library | attempts | complete | verified | unsupported | stopped by limit | failed |
|---|---:|---:|---:|---:|---:|---:|
| Zeebra | 288 | 211 | 0 | 56 | 21 | 0 |
| Singular | 140 | 120 | 0 | 5 | 14 | 1 |
| msolve | 110 | 62 | 0 | 39 | 5 | 4 |
| Groebner.jl | 110 | 55 | 0 | 50 | 5 | 0 |
| Sagebrush | 162 | 130 | 0 | 17 | 14 | 1 |
| groebner-rs | 100 | 0 | 96 | 0 | 4 | 0 |
| **total** | **910** | **578** | **96** | **167** | **63** | **6** |

These are retained attempts, including repeated arms and intentional refusal controls, not counts
of distinct solved instances. `verified` is the stored outcome of the independently checked
submitted groebner-rs bases; it is kept separate from `complete` rather than rewriting history.
The tasks comprise 582 reduced-basis, 268 lex-by-conversion and 60 eliminant attempts.

Environment cohorts are kept separate: 545 rows use `ZEEBRA_MACHINE=workstation`, affinity `0-7`;
164 use `fedora`, affinity `2`; 196 use `trpro-5995wx`, affinity `0-3`; five historical `fedora`
rows have affinity **unset**. Affinity is recorded in `environment.cpu`. Missing affinity is
incomplete evidence, not implicit pinning. Policy, digest, field, worker count, task and provenance
must agree before a ratio is considered. Startup floors, stage resolution, invariant overlap,
equivalence and ISA authority still gate conclusions; historical Sagebrush rows remain visible
beside the matched-ISA re-take. No aggregate win count across these cohorts is an engine ranking.

#456's second task is now executable at supported primes and retained: of 60 eliminant attempts,
Zeebra completes 11, Singular 10 and msolve 7. Unsupported adapters, positive-dimensional inputs,
a Singular limit stop and four historical msolve failures remain in the history. This adds a
comparison objective; it does not establish parity with msolve. #678 adds a pinned MIT Rust
comparand with verified basis submissions, rather than relabeling a solution as a basis.

### 15.3 Performance and memory: what shipped

The final F4 decision is [interreduction §3h](research/interreduction-cost.md#3h-575-the-2x2-over-both-flags-and-both-defaults-move),
cohort `3d0e3759`, `ZEEBRA_MACHINE=workstation`, `ZEEBRA_AFFINITY=0-7`, one worker, under
`benchlock`, one row per process. Both flags are crossed in one cohort; no ratio below spans
historical sessions. Recommended options now use `reduce_batch_rows: true` and
`interreduction: InterreductionRoute::ByOrder`. Baseline options retain the earlier settings.

| full reduced-basis task | old default | shipped pair | Singular | paired improvement | lead over Singular |
|---|---:|---:|---:|---:|---:|
| `mq-random-10` | 27 536.2 ms | 4 695.7 ms | 7 371.9 ms | 5.86x | 1.57x |
| `katsura-11` | 241 042.6 ms | 29 769.4 ms | 53 591.9 ms | 8.10x | 1.80x |

MQ uses three attempts per Zeebra arm; Katsura uses one and saw load excursions, so **Katsura is
the first result to repeat** before extending its quantitative claim. On the MQ cohort, msolve
and Groebner.jl remain faster. Removing the Singular deficit does not remove the remaining gaps.

Memory rises against the old defaults: MQ mean per-process peak RSS is **418.8 MiB versus
162.1 MiB**; Katsura is **667.0 MiB versus 538.9 MiB**. The source study labels these binary-scaled
values MB. Against matrix interreduction with unreduced batch rows, the pair reduces memory;
against the old default it increases it. #536's construction budgets and #554's retained-basis
removal made the route bounded enough to ship. Matrix-entry budgets are not whole-process RSS
limits. Lex still selects division; the graded-order win is not a universal interreduction rule.

A later capability is [certified scalar Wiedemann conversion](research/certified-wiedemann.md),
measured at base `4bcf3923` plus patch `621e87a0747fa855372cfc7c68accc4b8e76a7df`,
`ZEEBRA_MACHINE=5995wx`, `ZEEBRA_AFFINITY=2`, one worker. On its public sparse shape-position
family, the paired conversion ratios are **4.28x at quotient dimension 625** and **23.75x at
3 125**, including operator construction and independent certification. At 3 125, separate-route
processes measure **161 603 584 bytes** classical peak RSS and **5 660 672 bytes** adaptive.
These are conversion measurements, excluding basis computation and point recovery. They do not
establish whole-solver scaling or a universal route crossover. Adaptive attempts retain classical
fallback for nonseparating coordinates, exhausted projections, certificate failures or workspace
refusal. The M26 report's missing-converter statement describes its earlier snapshot.

### 15.4 New capabilities, frontier and remaining barriers

The corpus now has the second reference prime, extended affine Katsura/Cyclic ladders and
`GF(2)` Cyclic invariant checks. The eliminant sweep provides a second externally checked task;
the board has resolution-aware internal-time comparisons, enforced equivalence gates, matched-ISA
Sagebrush evidence and a verified groebner-rs adapter. F4 exposes per-batch degrees and budget
refusals through diagnostics. These are library and comparison capabilities.

Cryptanalytic position by `Official`, `FaithfulReduction` and `Engineering` class is **outside
this report's active scope after #668**. No class totals, witness, named slice or seed completion
is asserted. The previous research tree is `9532a9a2`. A larger corpus rung or faster basis does
not itself advance any of those classes. Against M26, the demonstrated change is competitive basis
performance and certified conversion, not a new challenge frontier.

A next larger instance may still refuse in F4 construction before conversion. #557's exact demand
diagnostic and [F4 resource scaling](research/f4-resource-scaling.md) identify that boundary; a
faster converter cannot remove it. The [algorithm decision](research/m27-algorithm-decision.md)
also identifies a planner boundary: `solve_one_planned` still preflights classical dense blocks,
so adaptive conversion workspace alone does not prove the planned entry point reaches the fast
route. #273's multi-family objective validation, #268's sparse-many-variable crossover and #439's
broader engine study remain unfinished. They are not silently closed by the milestone's goals.

### 15.5 Negative results and prediction accuracy

- **Matching batch counts did not imply matching intermediate objects.** #447 rejected extra work
  at its observed counts, but #477 found reducible tails accruing debt to final interreduction.
  The proposed matrix pass was estimated near 170 ms and first measured 4 094 ms, about 24x out;
  the autoreduction matrices differed by 405x in cells. Later quieter A/Bs measured a smaller
  stage cost. The estimate failed because the object being priced was wrong.
- **A stage share did not prescribe the storage remedy.** #304's copy removal did not remove
  interreduction time. The baseline records that correction; the isolated old storage before/after
  RSS pair remains missing. It cannot be supplied by a different route's memory measurement.
- **The headline matrix speedup was session-sensitive.** The baseline carries forward its paired
  3.63x, not the loaded cohort's 4.18x. Its approximately 7 999 ms projected matrix total was later
  measured at 8 333.1 ms, 4.2% out, in a new cohort. This is a checked prediction, not permission
  to divide an old denominator into a new result.
- **The flags interact.** Matrix routing alone was nearly worthless on budget-refused Katsura-11;
  reducing batch rows made its closure affordable. Neither independent flag predicts the pair.
- **Cached public monomial degree was rejected.** [#317's retained experiment](research/monomial-degree.md)
  found no material stage-level improvement under its gate. The initial §13 claim that agreeing
  counts would make monomial representation the highest-leverage change did not survive testing.
  #268's sparse-support experiment remains a distinct open question.
- **Repeated division work did not justify caching.** [Interreduction §3i](research/interreduction-cost.md#3i-569-candidate-2-counted--9857-of-the-steps-repeat-and-it-is-the-cheap-half-that-does)
  confirms repetition, but the shipping MQ route executes zero such division steps. A high repeat
  percentage is not a measured product opportunity.
- **M27-D's refusal is the deliverable.** No current-default whole-solver profile prices a useful
  XL, Hilbert or ordering prototype on the target. Existing Wiedemann conversion is not an XL
  solver. A storage model and a historical basis-only gain do not price verified point recovery.

### 15.6 M28 recommendation and the original hypotheses

**Run first:** repeat the weak Katsura measurement and collect a bounded current-default profile
on public MQ, including basis, operator construction, conversion, point recovery, verification and
attributable process RSS. Build before measurement, use a single recorded environment, retain
refusals, and charge fallback work. Reuse the [#457 pilot limits](research/m27-algorithm-decision.md#5-what-would-change-the-decision)
rather than authorizing a larger campaign from this report. This resolves whether remaining F4
construction or conversion/planner integration actually limits the complete solve.

The competing investment is #273: adaptive conversion has measured benefits on one family, while
its planned entry point can reject on dense preflight. Compare complete routes and objectives
before changing that policy. #268's representation experiment competes only after a current
profile identifies the memory traffic it could remove; the old 80.4% stage share cannot fund it.
Variable ordering remains the cheapest bounded candidate to measure if the full-route profile
supports it. XL requires construction, recurrence and verified recovery costs, not only columns.

| initial §13 hypothesis | score at this snapshot | consequence |
|---|---|---|
| 1: agreeing work counts make monomial representation the top lever | **premise confirmed; remedy rejected as a general conclusion** | Batch-tail reduction and matrix interreduction shipped; #317's cache failed its stage gate. Re-profile before another representation change. |
| 2: disagreeing counts fund pair handling/HDF4 | **antecedent false** | #447 observed agreement; no funding follows from this branch. |
| 3–4: challenge barrier and XL hypothesis | **moved out of scope** | Preserved at `9532a9a2`; no library-only result answers the moved campaign question. |
| 5: historical ordering gains justify a default | **not established** | #457 requires current public-family whole-route evidence; keep a measured pilot separate from a default change. |

Project #7 was read directly, with all 333 items returned at review: all 50 M27-labeled issues
have project rows, and every closed one is Done. #458 is In Progress during this work; #450,
#256, #268, #273 and #439 remain open. Parent relationships are preserved. The two original
housekeeping notes are historical: #223 and #274 are already closed. No issue is closed merely
because this report lists its result. Remaining uncertainty is explicit: multi-family conversion
crossover, present full-solver bottlenecks, isolated old storage RSS and a new challenge frontier
are not measured here.
