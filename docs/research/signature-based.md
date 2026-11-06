# Signature-based criteria: a ~2× ceiling, measured, and a won't-do

Deliverable for B5 (#223), a child of the MQ-algorithms epic #66. B5's instruction was to read the
ceiling off instruments that already exist before contemplating an implementation, because **the upper
bound on what any selection-strategy change can win is already measured and had never been read
off.** This is that reading. No new code; four existing examples, plus five papers — including F5's
own (§4.4) and the survey that closes the citation chain and retracts one of this document's own
arguments (§4.0.1, §4.2, §5.1).

**The headline: 33–60% of F4's pair rows add no rank, which bounds the whole direction at about 2×,
and a ~2× constant factor does not justify adopting the signature apparatus.** Recorded as a
won't-do in the style of #58. **Nothing is left open** — the one question §5.1 held back resolved
negatively once the survey was read, and every source #223 named is now read.

**Revision note.** The first version of this document reported the ceiling and recommended "spike
further, narrowly — neither implement nor decline", because it had not read Ding, Zhang and Deaton,
*How Much Can F5 really Do?* (eprint 2021/051). That paper measures the same quantity on different
instances, **agrees with the measurement**, and supplies the structural reason a ~50% row reduction is
worth little: F4 and F5 reach the same degree of regularity, so signatures remove rows and never
columns, while complexity is driven by the degree. §4.0 is the engagement and §5 is the revised
recommendation. The original reading is left visible in §6 rather than edited away — the ceiling was
measured correctly and interpreted backwards, which is a more useful thing for a later reader to see
than a clean document.

## 1. What is being measured, and against which engine

"Redundant work" is not one quantity. Three distinct ones, and conflating them is how the F5
literature's claims get overstated:

1. **Pairs discarded before reduction**, by Buchberger's product criterion, the chain criterion and
   Gebauer–Möller. Free — they never become matrix rows. `examples/pair_criteria.rs`.
2. **Reductions that produce zero**, under classical one-pair-at-a-time Buchberger. This is the
   quantity F5's guarantee is stated about — F5 computes **no** zero reductions for a regular
   sequence. `examples/f4_statistics.rs`' `bb:0` column.
3. **Pair rows that add no rank**, under F4 as shipped. F4 batches many pairs into one matrix, so it
   has no "reduction to zero" as an event; the analogue is a row that contributed nothing to the
   rank. `examples/f4_degrees.rs`.

**(3) is the one that bounds what a signature criterion could win here**, because Zeebra ships F4
with Gebauer–Möller already on. (2) is what the literature quotes. The two differ by more than an
order of magnitude, and a proposal that cited (2) as Zeebra's headroom would be wrong by that much.

## 2. Gebauer–Möller already discards most pairs

`cargo run --release --example pair_criteria`, grevlex, over GF(2^31 − 1):

| system | pairs at `none` | pairs at `gebauer-moller` | discarded |
|---|---:|---:|---:|
| cyclic-4 | 45 | 11 | **76%** |
| cyclic-5 | 1035 | 116 | **89%** |
| katsura-4 | 36 | 11 | **69%** |
| katsura-5 | 105 | 30 | **71%** |
| katsura-6 | 276 | 68 | **75%** |
| katsura-7 | 903 | 166 | **82%** |

`all` is identical to `gebauer-moller` on every row, so Gebauer–Möller subsumes the product and chain
criteria on this corpus rather than composing with them.

**So the baseline a signature criterion has to beat is not a naive Buchberger. It is an F4 that has
already thrown away 69–89% of its pairs.** Any new criterion operates on the 11–31% that survive.

## 3. The ceiling: pair rows that add no rank

`cargo run --release --example f4_degrees` — the M22 instrument, which reports this per instance
alongside the rank the pair rows added on top of the reducer block. Configuration:
`F4Options::recommended()`, grevlex, `max_matrix_columns = 60_000`, `max_live_bytes = 400 MB`.

Rank attribution is exact and the example says why: reducer rows have distinct leading monomials and
so span a space of dimension exactly `reducer_rows`, which makes `rank − reducer_rows` the pair rows'
contribution, independent of the order elimination took them in.

| class | instance | vars | eqs | pair rows adding no rank | mutants |
|---|---|---:|---:|---:|---|
| classical | katsura-5 | 5 | 5 | **40.0%** (24/60) | 0 of 5 batches |
| random MQ | Fukuoka III `n=10` | 10 | 20 | **54.2%** (806/1486) | 65 over 1/6 |
| random MQ | Fukuoka III `n=15` | 15 | 30 | **55.0%** (3955/7192) | 335 over 2/7 |
| random MQ | Fukuoka VI `n=10`, as published | 10 | 7 | **58.9%** (390/662) | 0 of 7 |
| random MQ | Fukuoka VI `n=10`, specialized | 10 | 10 | **59.8%** (397/664) | 0 of 8 |
| structured CICO | Poseidon `t=2 R_F=2 R_P=0` | 5 | 5 | **33.3%** (26/78) | 8 over 5/9 |
| structured CICO | Poseidon `t=2 R_F=2 R_P=2` | 7 | 7 | **48.5%** (397/818) | 37 over 8/13 |
| structured CICO | Poseidon `t=2 R_F=4 R_P=0` | 9 | 9 | **53.6%** (961/1794) | 80 over 17/22 |
| structured CICO | Poseidon `t=3 R_F=2 R_P=1`, pinned | 9 | 9 | **46.0%** (183/398) | 38 over 7/11 |
| structured CICO | Poseidon `t=3 R_F=2 R_P=1`, as generated | 9 | 8 | **57.5%** (2849/4954) | 164 over 12/20 |

The MQ rows need `tools/fetch-mq-challenge.sh`; the rest run without it.

Three readings:

- **The ceiling is 33–60% everywhere.** There is no instance class where it is negligible. B5
  anticipated "if zero reductions are 2% of the work on the cryptanalytic systems, F5 is declined on
  the existing data" — that branch does not apply.
- **It rises with difficulty.** On the Poseidon family at fixed state width, 33.3% → 48.5% → 53.6%
  as rounds increase; the hardest row, the one that crosses the column budget after 18.2 s, is the
  worst at 57.5%. On Fukuoka it is 54–60% at both sizes. **The redundancy grows exactly where the
  solver is already failing**, which is the least convenient possible shape.
- **The structured instances are not worse than the random ones.** 33–58% against 54–60%. The
  cryptanalytic systems are *not* distinguished by having more redundant rows, which is mildly
  surprising and worth recording, since it is a difference the Hilbert-driven work (#74) does find
  between these classes.

### 3.1 Mutants, cross-checked

`docs/research/mutants.md` §2's finding — mutants are "common on the cryptanalytic systems and absent
on the classical ones" — reproduces exactly: 0 on katsura-5, 8 to 335 on every Poseidon row and on
Fukuoka type III. Two new observations from the same table:

- **Fukuoka type VI has no mutants at all**, as published or specialized, while type III has many.
  Same field, same challenge, different shape — type VI is the underdetermined signature family. So
  "cryptanalytic" is not the predictor; something about overdetermination is.
- Type III's mutants arrive in **1 or 2 batches out of 6–7** but number 65 and 335, while Poseidon's
  arrive in most batches in smaller groups. Different phenomena wearing one name.

Neither changes `mutants.md` §5's decision. Both are relevant to #74, which owns that question.

## 4. Why the ceiling does not settle it, and what does

A 33–60% ceiling says a perfect selection criterion could remove up to about half the pair rows. It
does **not** say F5 would, and four structural facts weigh against it. This is where B5 is decided.

**§4.0 was added after the fact and supersedes the first draft's reading of this section.** The first
version of this document recommended "spike further, narrowly" partly because the decisive source had
not been read. It has now, it agrees with §3's measurement, and it draws the conclusion §3 stopped
short of.

### 4.0 Ding, Zhang and Deaton measured the same thing, and it is the whole argument

Ding, Zheng Zhang and Deaton, *How Much Can F5 really Do?*, eprint 2021/051 — **read 2026-11-06**,
from a local copy. B5 required this source to be engaged rather than cited, and the first draft of
this document did not engage it. This section is that engagement.

**Their quantity is this document's quantity.** §5 of the paper: "Here we record our experimental
results on how many rows reduce to zero in the largest matrix in the F4 algorithm." Same measurement,
independent implementation, independent instances — random homogeneous quadratic systems over `F2`
with and without field equations, and HFE public keys with `D = n`.

**Their numbers agree with §3's**, which is the strongest thing in this document because neither
measurement knew about the other:

| their system | `n` range | zero-row proportion |
|---|---|---|
| homogeneous random quadratic, **with** field equations (their Table 1) | 2–13 | 0.243 – **0.617**, with outliers at 0.014–0.021 |
| homogeneous random quadratic, **without** field equations (Table 2) | 2–9 | 0.25 – **0.559** |
| HFE with `D = n`, with field equations (Table 3) | 5–14 | 0.257 – **0.613**, with outliers at 0.024–0.027 |

Against §3's **33–60%** on Fukuoka, Poseidon and katsura. Their summary, verbatim: "the highest
proportion of zero rows is approximately **0.617** with many of the matrices being slightly higher
than half of zero rows."

**And the argument that makes the ceiling decisive rather than encouraging** — their §4.1, verbatim:

> We note that the degree of regularity for F4 and F5 are the same `D_reg` [30], the matrix that F5
> and F5 inspired algorithms will be working with is **essentially the same size as F4 but having
> fewer rows** due to the use of signatures.

With complexity approximately `C(n + D_reg, D_reg)^ω`. So:

1. F4 and F5 reach the **same degree of regularity**, hence the same **column** count.
2. Signatures remove **rows only**, by a factor the measurement bounds at about two.
3. Therefore **F5 cannot change the complexity exponent at all** — it is a constant-factor win on a
   quantity driven entirely by `D_reg`, which it does not touch.

Their conclusion: "If this pattern holds for larger values of `n`, then **the F5 algorithm should not
be much better than twice as fast as F4.** As often the strength of cryptosystems are measured in the
hundreds of bits, having no zero row reductions would be **a modest increase in efficiency**."

**That reverses the sign of §3 as an argument.** A ~50% ceiling is not headroom worth a rewrite; it is
an upper bound of ~2× on a problem whose difficulty is measured in powers of two. §3's finding that
the ceiling *rises with difficulty* does not help either, because it rises toward ~0.6 and stops — the
bound is a bound.

**One methodological difference, and it favours this document's numbers.** They measure the single
largest matrix, and say so twice: "Note that this is not necessarily the matrix with the largest
percentage of zero rows." That makes their estimator noisy, and visibly so — Table 1's `n = 10, 11, 12`
read 0.021, 0.018, 0.014, and Table 3's `n = 13, 14` read 0.027, 0.024, which they explain as
"Sometimes, we are lucky and almost all of the rows are non-zero". `examples/f4_degrees.rs` aggregates
**every** pair row across the whole computation, so §3 has no such artifact. The two agree on the
range anyway, which is the point.

**The load-bearing step, now checked.** The "same `D_reg` for F4 and F5" claim is attributed to their
reference [30] — Yeh, Cheng and Yang, *Operating Degrees for XL vs. F4/F5 for Generic MQ with Number
of Equations Linear in that of Variables*, in *Number Theory and Cryptography*, Springer 2013,
pp. 19–33. **Read 2026-11-06.** It says, verbatim:

> `F4/F5`: It suffices to know that these are "better" versions of XL2 where the matrix-building and
> row-operation sequences are run according to certain rules to avoid redundancy, but
> **`F4/F5/XL2` all run at the same degree** [27], which is `D_reg` for semi-regular systems.

So the claim is confirmed — **with two qualifications that have to be stated, and neither overturns
the conclusion.**

1. **They assert it rather than prove it**, with "It suffices to know that", and cite it onward to
   their own [27] (Yang and Chen, *All in the XL Family: Theory and Practice*, ICISC 2004).
   **Read 2026-11-06, so the chain is now closed; see §4.0.1.**
2. **They gloss it with "which is `D_reg` for semi-regular systems"**, and §4.1 of this document
   establishes that Zeebra's targets are *not* semiregular. Read narrowly, the quoted sentence is
   therefore about a class Zeebra's instances are outside.

#### 4.0.1 The chain, closed — and the published claim is narrower than the one used here

Yang and Chen's **Proposition 4** proves the first half and attributes the second:

> We have shown that **XL+XL2 and F5 operates at the same apparent degree `D_g`.** Further ([30]) the
> signature, i.e. the underlying degree, of the polynomials in the matrix/system built by **F5 is the
> same as the classical Buchberger algorithm, which is the same as classical XL**.

Their **[30] is Faugère's ISSAC 2002 F5 paper** — read for §4.4. So the citation chain terminates and
every link in it has been read: 2021/051 → Yeh–Cheng–Yang → Yang–Chen → Faugère 2002.

**But the published statement carries hypotheses the conclusion here does not.** Proposition 4 is
stated **"for large `q`"**, and the surrounding Eq. 5 holds "for all `D < min(q, D_reg)`" with

`D_reg := min{D : [t^D] (1 − t)^(m−n−1) (1 + t)^m ≤ 0}`

— the large-field degree of regularity. Yeh et al. then added "which is `D_reg` for semi-regular
systems" on top. So the cited support is **weakest exactly where much of this crate's corpus lives**:
Fukuoka types I, II and IV are over `GF(2)`, types III and VI over `GF(31)`, LowMC and HFE over
`GF(2)` — none of them "large `q`". That eprint 2021/051's §4.2 gives *two* `D_reg` formulas, one for
`D_reg ≤ q` and one for `D_reg < q`, is the same point from the other side.

**The decline is unaffected, because it uses none of that.** The argument below is that F4 and F5
compute the same reduced basis under the same order, so the maximum degree in it is a property of the
ideal and no algorithm computing it can avoid that degree — true over any field, large or small. What
the literature supplies is a *formula* for what the degree is, and the formula is what carries the
hypotheses.

Worth stating plainly because the shape is unusual: **the published version of the equal-degree claim
is narrower than the version this decline rests on, and the version it rests on is elementary.** That
is a better position than depending on the citation would have been.

**Why the conclusion survives qualification 2, and this is reasoning rather than citation.** F4 and
F5 compute **the same object** — the reduced Gröbner basis of the same ideal under the same order.
The maximum degree occurring in that basis is a property of the ideal and the order, not of the
algorithm that finds it, so no algorithm computing it can avoid processing that degree. The "same
operating degree" conclusion is therefore forced independently of semiregularity; what semiregularity
buys is the *formula* for what that degree is, which this argument does not need. The clause worth
keeping from Yeh et al. is the first half — signatures change "the matrix-building and row-operation
sequences … to avoid redundancy" — which is precisely a statement that they remove rows and not
columns.

So: cited, now read, confirmed, and the one gap it leaves (Yang–Chen ICISC 2004) does not carry the
argument, because the argument can be made directly.

### 4.1 The guarantee does not transfer

F5 computes no zero reductions **for a regular sequence**. Zeebra's targets are not regular and not
even semiregular: `docs/research/hilbert-driven.md` §3 measures the semiregular prediction as **27×
wrong on Poseidon**, and `docs/research/hilbert-functions.md` records where the Fukuoka and Poseidon
families depart from it. So the theorem that motivates F5 is silent on exactly the instances this
crate is aimed at, and only the empirical ceiling of §3 survives as evidence.

Read the ceiling and the regularity failure together and they point the same way: redundancy is
*highest* on the systems where the structural theory is *least* applicable.

### 4.2 Signatures and batched echelonization are in tension

The substantive obstacle, and the analogue of #58's reasoning for Wiedemann.

Classical F5 is incremental and polynomial-at-a-time. Zeebra's F4 batches many pairs into one
Macaulay matrix and echelonizes it — M16-A's Faugère–Lachartre split and M16-B's symbolic
preprocessing are both built around that. A signature attached to a matrix *row* has to survive
elimination, and elimination **combines rows**. Matrix-F5 exists to reconcile the two, and whether its
reconciliation fits Zeebra's row arrangements is the open question.

`examples/f4_blocks.rs` already shows why this is not a detail: it replays real matrices under four
row arrangements and the computed candidates differ between them, because "a change of row arrangement
changes which candidates come out, hence every later batch". A signature discipline is a constraint on
row arrangement. So it does not compose with the arrangement freedom F4 currently exploits — it
competes with it.

Modules it would touch, named as B5's question 5 requires: `grobner/pairs.rs` (signature-ordered
selection), `grobner/f4/symbolic.rs` (reducer selection constrained by signatures rather than chosen
for efficiency), `grobner/f4/macaulay.rs` (rows carrying signatures), `grobner/f4/reduction.rs` (row
operations preserving or combining them). That is the whole of F4's core, which makes it a rewrite
rather than an optimization — and `#58`'s precedent is to record that and decline.

> **Retracted, 2026-11-06. The "rewrite rather than an optimization" claim is overstated, and the
> survey says so.** Eder and Faugère's §13, *s-reductions using linear algebra*, is directly about
> hosting signature criteria inside F4-style reduction:
>
> "Here we present a variant of F4 that uses signature-based criteria to detect reductions to zero
> resp. rows reducing to zero in advance. This leads to **smaller changes in the implementation of
> some subalgorithms of F4** corresponding to the switch from usual polynomial reduction to
> s-reduction. Albrecht and Perry describe a possible implementation of this, called **F4/5**."
>
> So an F4-hosted signature variant is published, implemented, and characterised as *smaller changes
> to some subalgorithms*. Two of its stated differences (Algorithmic Property 13.1) are even
> favourable: F4/5 proceeds **by increasing degree rather than by index** — the module order `<d-pot`
> rather than `<pot` — which is what Zeebra's F4 already does, and it orders generators by increasing
> rather than decreasing index.
>
> **This paragraph's module list may still be right about what gets touched; its conclusion about the
> magnitude is not, and it was my inference rather than anything a source said.** The decline does
> not depend on it — §4.0's ~2× bound and §4.4's overconstrained argument are each sufficient — so
> the retraction removes a leg the conclusion was not standing on.
>
> One related note from the same survey, which matters if this is ever revisited: **MatrixF5 is the
> wrong variant for this crate regardless.** "MatrixF5 … is efficient once the system of polynomial
> equations is **dense**. Clearly, this is not always the case, and thus, selecting S-pairs to be
> reduced is more convenient compared to building full Macaulay matrices at a given degree."
> `examples/elimination_density.rs` measures Zeebra's global densities at a fraction of a percent, so
> F4/5 and not MatrixF5 would be the shape. MatrixF5 also needs a **degree bound `D`** as an extra
> parameter, which `f4/hilbert_driven.rs` does supply.

A further casualty: `examples/f4_selection.rs` prices two reducer-selection policies and three cache
modes. Under a signature algorithm the reducer choice is constrained by signatures, so those policies
may become **invalid rather than merely suboptimal**, and the M16/M19 investment in them would not
carry over.

### 4.3 The one external data point, reconciled

From Allan Steel's Magma Gröbner-basis timings page, read in place on 2026-11-06 (see #199): for
**Cyclic 10 over GF(32003)**, Magma's optimized F4 took **17.6 days** on a 750 MHz Sunfire v880 using
30.7 GB, and the page records that

> no-one else has successfully computed this Gröbner basis except for J.-C. Faugère, as explained in
> his F5 paper [ISSAC 2002], where he took **16 hours on a 1GHz PIII** (using the unpublished improved
> **F5'** algorithm).

**Read on its own that is a ~26× advantage for an F5-family algorithm on identical input** — the
published F4-versus-F5 comparison #223 said the corpus lacked, and it favours F5 substantially.

Three cautions that stop it being decisive, and they matter:

- **F5' is unpublished and improved.** The page says so. Whatever did this is not the F5 of the 2002
  paper, so it is not a specification anyone could implement from.
- **Cyclic-10 is not a cryptanalytic system.** It is the classical family, where §4.1's regularity
  objection is weakest and F5's guarantee most nearly applies. The transfer to Poseidon or Fukuoka is
  exactly what is unsupported.
- **Different machines, different years.** 17.6 days on a 750 MHz Sunfire against 16 hours on a 1 GHz
  PIII is not a clean 26×; §4 of #199 argues no 2004 wall-clock ratio is clean.

**And §4.0 now reconciles it, which is the more useful outcome than cautioning about it.** If F4 and
F5 reach the same `D_reg` and signatures remove rows by a factor of about two, then **an algorithmic
26× is impossible** and most of that ratio must be something other than the signature criterion:
Faugère's own implementation against Magma's, a different reduction strategy, or the "improved"
part of the unpublished F5'. The Cyclic-10 figure is therefore evidence about **two implementations**,
not about what signatures buy — and read that way it stops being the one data point favouring F5.

That is the right reading to carry forward. A 26× that cannot be attributed to the mechanism under
consideration is not support for adopting the mechanism.

### 4.4 Faugère's own paper settles it, and adds the sharpest argument against

The reconciliation above was an inference from §4.0's bound. The **primary source** has since been
read — Faugère, *A new efficient algorithm for computing Gröbner bases without reduction to zero
(F5)*, ISSAC 2002, Ver 1.2 — and it does not need inferring. Figure 9.2, Cyclic `n` modulo `p` on an
"Inspiron PIII 1Ghz", CPU seconds:

| Cyclic | 7 | 8 | 9 | 10 |
|---|---:|---:|---:|---:|
| F4 | 1.26 | 36.0 | 4949.1 | — |
| F4 inc | 1.4 | 171.3 | — | — |
| **F5** | **1.0** | **27.9** | — | — |
| F5′ | 0.4 | 7.2 | 1002.3 | **57600** |
| F5″ | 0.8 | 3.95 | 676.2 | — |

`57600 s = 16 hours`, which places Steel's independently reported figure in the **F5′** row — the
unpublished improved variant — and not in F5's.

**Basic F5 against F4 is 1.26× on Cyclic 7 and 1.29× on Cyclic 8.** That is inside §4.0's ≤2× bound,
from the algorithm's author, on the family §4.3 had to reach for. So §4.3's "most of that ratio must
be something other than the signature criterion" is no longer a deduction: the author's own table
separates basic F5 from F5′, and the paper defers F5′ and F5″ to "a future paper".

**And the paper supplies an argument the decline did not have, which is the sharpest one here:**

> The algorithm F5 is **not always faster** than F4: for cyclic `n` the basic version of the F5
> algorithm is **just a little faster than F4**; the maximal efficiency of the F5 algorithm is
> expected when the number of equations is **less or equal than** the number of variables. On the
> contrary **bad performance is expected when the system is overconstrained**.

**Zeebra's MQ targets are overconstrained by construction.** Fukuoka type III is `m = 2n` — 20
equations in 10 variables, 30 in 15 — and it is the type Zeebra has verified witnesses on. For the
encryption families on the record board, the designer of F5 expects it to **lose** to F4. §3's
ceiling bounded the prize at ~2×; this says that on a large part of the target corpus the prize is
*negative*. Note the shape of §3's own table is consistent with that and nobody noticed: the
overdetermined Fukuoka type III rows carry 54–55% redundancy, the underdetermined type VI rows
58–60%, and type VI is the family where the equation count is *below* the variable count.

One more cap from the same source, §9.1, on the quantity §1 distinguishes as (2):

> reductions to zero are unavoidable for [one example]… By reformulating these problem we obtain an
> equivalent system with no reduction to zero! The conclusion is that **for a lot of practical
> examples there is no reduction to zero**.

**Not quoted from this paper:** its Katsura figures. The text extraction merges two tables both
captioned "Fig 9.2: Katsura n" — one in CPU seconds, one in speedup — and the columns interleave, so
which is which cannot be established from the extraction. The Cyclic table is unambiguous and
externally corroborated; the Katsura one is left alone rather than guessed at.

## 5. Recommendation

**Decline the F5/Matrix-F5 direction for Zeebra's F4. Keep one narrow question open.**

This revises the first draft, which recommended "spike further, narrowly, neither implement nor
decline" while eprint 2021/051 was unread. With it read, the evidence points one way:

- **The win is bounded at about 2×, and bounded for a structural reason.** F4 and F5 reach the same
  degree of regularity, so the matrix has the same columns and F5 removes only rows (§4.0). The
  complexity exponent is driven by `D_reg`, which signatures do not touch. Against difficulty measured
  in powers of two, the authors' own phrase is the right one: "a modest increase in efficiency".
- **On the overdetermined half of the corpus the expected win is negative**, per F5's own author:
  "bad performance is expected when the system is overconstrained" (§4.4). Fukuoka types I, II and
  III are all `m = 2n`.
- **The measured ceiling confirms the bound rather than challenging it.** §3's 33–60% and their
  0.24–0.62 are the same answer from two independent measurements. §3's observation that the ceiling
  *rises* with difficulty looked like an argument for F5 in the first draft; it is not, because it
  rises toward ~0.6 and stops.
- **The one favourable data point dissolves on inspection**, and the primary source confirms it
  rather than merely permitting the reading: Faugère's own Figure 9.2 puts basic F5 at **1.26–1.29×**
  over F4 and attributes the 16-hour Cyclic-10 run to the unpublished **F5′** (§4.3, §4.4).
- **The cost is a rewrite of F4's core** — `pairs.rs`, `f4/symbolic.rs`, `f4/macaulay.rs`,
  `f4/reduction.rs` — and it may invalidate rather than merely pessimize the reducer-selection
  policies M16 and M19 priced (§4.2).
- **The guarantee does not apply to the target systems anyway** (§4.1).

A ≤2× constant factor, for a rewrite of the core, on instances where the motivating theorem does not
hold. Recorded as a **won't-do in the style of #58 and of `docs/research/mutants.md` §5**, so the
question is not reopened without new evidence. New evidence would be: a published signature-based
result that changes `D_reg` rather than the row count, or a measurement showing the ≤2× is worth more
than it appears because rows dominate Zeebra's cost in a way they do not dominate the complexity
model.

### 5.1 The one question that stays open

**Assess GVW as a *criterion*, inside `pairs.rs`, and nothing more** (B5's question 6). The rewritable
criterion is reported as simpler than F5's and as subsuming it, and the point is that it is a pair
criterion rather than an algorithm — so it could sit beside Gebauer–Möller without the §4.2 rewrite,
and `examples/pair_criteria.rs` already exists to price it against GM on one table.

This survives the decline above because it is cheap and because §2 leaves room for it: Gebauer–Möller
discards 69–89% of pairs, and §3 shows 33–60% of what *survives* still adds no rank. **Whether a
rewritable criterion catches any of that residue is unknown and is the only thing left worth
measuring.** It is a bounded question with an existing instrument, and it does not commit the crate
to anything.

> **Resolved negatively, 2026-11-06. The premise was wrong: GVW's rewritable criterion is not a
> standalone pair criterion.** Eder and Faugère's survey has been read, and it is defined on
> **signatures** `s(α)`, under a **module monomial order on `R^m`** rather than a monomial order on
> `R`, and its rewritability check — their Algorithm 3 — takes the S-pair together with **`G ∪ H`**
> and a **rewrite order `⋗`**, where `H` is a Gröbner basis for the **syzygy module** and Koszul
> syzygies are added to it explicitly (their Algorithm 2, line 3). A *rewrite basis* is defined by the
> canonical rewriter in a signature not being regular top s-reducible.
>
> So the criterion **presupposes the entire signature apparatus** — a signature on every basis
> element, a compatible module order, and a tracked syzygy basis. **There is no criterion-without-the-framework
> to graft beside Gebauer–Möller**, which is exactly what this section proposed.
>
> The survey also places F5's criterion *inside* the same framework rather than as an alternative at a
> different cost: Remark 6.5 — "Restricting Lemma 6.4 to principal syzygies and the compatible module
> monomial order `<pot` we get a statement **equivalent to the F5 criterion**". Its Table 1 lists GVW
> as generalizing G2V, with SB and SSG "coincid[ing] with GVW". One family, one apparatus.
>
> **So nothing is left open and this document is a complete won't-do.** The residue §2 and §3 identify
> is real, and no cheap criterion is available to attack it.

What should **not** happen: any change to `f4/reduction.rs` or `f4/macaulay.rs`, and any work
predicated on F5 being asymptotically better than F4. It is not.

## 6. What this did not do

- ~~**eprint 2021/051 was not read.**~~ **Closed** — read 2026-11-06, and §4.0 is the engagement. It
  changed the recommendation from "spike narrowly" to "decline", so leaving it unread had been the
  single largest gap in the first draft. Recorded rather than edited away, because the shape of the
  error is instructive: §3's ceiling was measured correctly and *interpreted backwards* for want of
  the one source that says what a ~50% row reduction is worth.
- ~~**Yeh et al. [30] was not read.**~~ **Closed** — read 2026-11-06; §4.0 quotes it and records the
  two qualifications it comes with. The claim is confirmed; its own onward citation (Yang and Chen,
  ICISC 2004) is unread, but §4.0 shows the argument does not depend on it, since F4 and F5 compute
  the same basis and its maximum degree is a property of the ideal rather than of the algorithm.
- ~~**The Eder–Faugère survey was not read.**~~ **Closed** — read 2026-11-06. It resolved §5.1
  negatively (the rewritable criterion needs the whole signature apparatus) and **retracted §4.2's
  implementation-cost claim**, which was mine and was overstated.
- ~~**Yang and Chen, ICISC 2004, was not read.**~~ **Closed** — read 2026-11-06; §4.0.1. Its [30] is
  Faugère's ISSAC 2002 paper, read for §4.4, so **the chain terminates and every link in it has been
  read.** The published claim turns out narrower than the one used here, which §4.0.1 records.

**Nothing named by #223 is now unread.** The decline rests on three independent legs — the measured
ceiling (§3, corroborated on disjoint instances by 2021/051), the elementary equal-degree argument
(§4.0, which needs no hypothesis), and F5's own author on overconstrained systems (§4.4) — and on
none of the retracted or narrowed claims.
- **The overlap question (B5's question 2) is still not answered.** §3 gives the ceiling and §2 gives
  Gebauer–Möller's share, but not whether they overlap. It matters less than it did: §4.0 bounds the
  prize at ~2× however the overlap falls, so the question is now only about §5.1's narrow criterion
  rather than about the direction.
- **No Matrix-F5 specification was produced**, and under §5 none should be.
- **HFE was not used as a calibration instance**, and 2021/051 makes this more interesting rather than
  less: its Table 3 measures HFE with `D = n` and field equations at 0.257–0.613, so the family is
  already calibrated by someone else at the same quantity. #198 has since established that HFE
  Challenge 1's input system survives at `minrank.org/challenge1.txt` and that three reduced rungs
  (`HFE25_96`, `30_96`, `35_96`) are downloadable with published Magma times. A Zeebra row beside
  their Table 3 would be a three-way check — but §5 says the direction is declined, so this is now a
  **validation opportunity for `f4_degrees.rs` itself** rather than an argument about F5.
- **Nothing was measured over GF(2).** #218 has since made characteristic two work, so the HFE route
  above is open — and note that 2021/051's measurements are *all* over `F2`, so a like-for-like
  comparison needs it.

### 6.1 Two things 2021/051 supplies to other issues

Neither is about F5, and both are worth more to the issues they belong to than to this one.

- **A closed-form `D_reg` for random quadratic systems**, their §4.2, attributed to Yeh et al. — one
  formula for small fields (`D_reg ≤ q`) and one for large (`D_reg < q`), both as the first `d` where
  a stated series coefficient goes negative. `src/grobner/hilbert.rs` models semiregular sequences and
  `examples/hilbert_study.rs` compares prediction against measurement; this is a second, independent
  prediction to compare against on the Fukuoka families. **Handed to #74.**
- **A closed-form `D_reg` bound for HFE- and HFEv-**, their §4.3, attributed to Ding–Kleinjung and
  Ding–Yang, together with the statement that "In 2002, Faugere experimentally showed the degree of
  regularity of HFE is much lower than expected for a random system. For some instances of HFE, the
  systems can even be solved polynomially." **That is exactly the anomaly #198 proposes to measure**,
  with a formula to predict it rather than only an expectation that it exists. **Handed to #198**,
  where it upgrades the solving-degree experiment from "check it is lower" to "check it matches a
  published bound".

## 7. Reproducing

```sh
cargo run --release --example f4_degrees        # the ceiling, per instance
cargo run --release --example f4_statistics     # Buchberger's zero reductions, for contrast
cargo run --release --example pair_criteria     # what each existing criterion discards
cargo run --release --example pair_criteria -- buchberger
tools/fetch-mq-challenge.sh                     # needed for the Fukuoka rows only
```

`f4_statistics` pins itself to `F4Options::baseline()` and asserts the two engines agree wherever both
can run; `f4_degrees` runs under `F4Options::recommended()`. The counters are therefore taken from
computations whose correctness is independently established, which is what makes §3 a property of the
computation rather than of one configuration's accounting.
