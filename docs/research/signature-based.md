# Signature-based criteria: the ceiling, measured before anything is built

Deliverable for step 1 of B5 (#223), a child of the MQ-algorithms epic #66. B5's instruction was to
read the ceiling off instruments that already exist before contemplating an implementation, because
**the upper bound on what any selection-strategy change can win is already measured and had never
been read off.** This is that reading. No new code; four existing examples.

**The headline: the ceiling is 33–60% of pair rows, it is nowhere near small enough to close the
question, and it rises with instance difficulty.** That is the opposite of the cheap decline B5
thought likely. It is also not a reason to build F5 — §4 is the structural argument, and it is where
the issue is actually decided.

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
does **not** say F5 would, and three structural facts weigh against it. This is where B5 is decided.

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

A further casualty: `examples/f4_selection.rs` prices two reducer-selection policies and three cache
modes. Under a signature algorithm the reducer choice is constrained by signatures, so those policies
may become **invalid rather than merely suboptimal**, and the M16/M19 investment in them would not
carry over.

### 4.3 The one external data point, and it cuts the other way

From Allan Steel's Magma Gröbner-basis timings page, read in place on 2026-11-06 (see #199): for
**Cyclic 10 over GF(32003)**, Magma's optimized F4 took **17.6 days** on a 750 MHz Sunfire v880 using
30.7 GB, and the page records that

> no-one else has successfully computed this Gröbner basis except for J.-C. Faugère, as explained in
> his F5 paper [ISSAC 2002], where he took **16 hours on a 1GHz PIII** (using the unpublished improved
> **F5'** algorithm).

**That is a ~26× advantage for an F5-family algorithm over an optimized F4 on identical input** — the
published F4-versus-F5 comparison #223 said the corpus lacked, and it favours F5 substantially.

Three cautions that stop it being decisive, and they matter:

- **F5' is unpublished and improved.** The page says so. Whatever did this is not the F5 of the 2002
  paper, so it is not a specification anyone could implement from.
- **Cyclic-10 is not a cryptanalytic system.** It is the classical family, where §4.1's regularity
  objection is weakest and F5's guarantee most nearly applies. The transfer to Poseidon or Fukuoka is
  exactly what is unsupported.
- **Different machines, different years.** 17.6 days on a 750 MHz Sunfire against 16 hours on a 1 GHz
  PIII is not a clean 26×; §4 of #199 argues no 2004 wall-clock ratio is clean.

And the skeptical reading has to be heard before any of this is acted on: Ding, Zhang and Deaton,
*How Much Can F5 Really Do?* (eprint 2021/051), interrogates the F5 claims directly. **It was not read
for this document** — see §6.

## 5. Recommendation

**Spike further, narrowly. Do not implement, and do not decline.**

The evidence does not support either extreme:

- **Against declining:** a 33–60% ceiling that rises with difficulty, plus a published 26× on
  Cyclic-10, is too much to dismiss on existing data. B5's cheap-decline branch is closed.
- **Against implementing:** the guarantee does not transfer to the target systems (§4.1), the
  structural fit with batched echelonization is bad and would touch all four of F4's core modules
  (§4.2), and the one favourable data point is an unpublished algorithm on a non-cryptanalytic
  instance (§4.3).

The next step that would actually move it, in order:

1. **Read eprint 2021/051.** It is reachable as a PDF and it is the cheapest input with the largest
   potential to settle the question. It should have been in this document.
2. **Assess GVW specifically** (B5's question 6), via the Eder–Faugère survey. The rewritable
   criterion is reported as simpler than F5's and as subsuming it, and — the point — it is a
   *criterion* rather than an algorithm, so it may be adoptable inside `pairs.rs` without the §4.2
   rewrite. **If anything in this family is adoptable, it is this**, and the question is narrow.
3. **Measure the GM-signature overlap directly.** The ceiling of §3 counts rows that added no rank;
   it does not say whether a signature criterion would have caught *those specific* rows or only
   rows Gebauer–Möller already discards. `examples/pair_criteria.rs` and `f4_degrees.rs` together
   could answer this without implementing F5, and it is the measurement that would convert §3's
   ceiling into an actual expected win. **This is the real step-2 and B5 should be recut around it.**

Not recommended: anything that touches `f4/reduction.rs` or `f4/macaulay.rs` before step 3.

## 6. What this did not do

- **eprint 2021/051 was not read**, and B5 requires it to be engaged rather than cited. §4.3 and §5
  flag it as the first follow-up. Nothing here should be read as a verdict on the F5 claims.
- **The Eder–Faugère survey was not read**, so §5's GVW recommendation rests on its reputation rather
  than on its content.
- **The overlap question (B5's question 2) is not answered.** §3 gives the ceiling and §2 gives
  Gebauer–Möller's share, but not whether they overlap. That is §5's step 3 and it is the gap that
  matters most.
- **No Matrix-F5 specification was produced**, deliberately: B5 gates that behind steps 1–4 being
  favourable, and §4.2 is not favourable.
- **HFE was not used as a calibration instance.** #198 has since established that HFE Challenge 1's
  input system survives at `minrank.org/challenge1.txt` and that three reduced rungs (`HFE25_96`,
  `30_96`, `35_96`) are downloadable with published Magma times — so the F4-versus-F5 comparison this
  document had to reach for Cyclic-10 to find may be available on an instance F5 was actually built
  for. That is a better calibration than §4.3 and it is now cheap.
- **Nothing was measured over GF(2).** #218 has since made characteristic two work, so the HFE route
  above is open.

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
