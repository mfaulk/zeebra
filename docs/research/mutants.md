# Mutants: measured, and why no mechanism follows

Reference for M22-D (#74). Figures from

```sh
tools/fetch-mq-challenge.sh
cargo run --release --example f4_degrees
```

under `F4Options::recommended()` with `profile_degrees` and `measure_stages` set, grevlex
throughout.

## 1. What a mutant is here, precisely

The plan's §9.1 asks for the distinction to be kept: **the degree a relation was *generated* at is
not the degree of the relation**. A Macaulay matrix built from critical pairs of lcm degree `d`
contains reducer multiples whose monomials run below `d`, so an echelon row can come out with total
degree `e < d`. That row is a mutant.

Zeebra records the two separately. `BatchStatistics::batch_degree` is the lcm degree the batch was
selected at; `min_candidate_degree` and `max_candidate_degree` are the degrees of what came out;
`candidates_below_batch_degree` counts the mutants. Nothing in this milestone equates a batch degree
with a polynomial degree, and `F4Statistics` keeps `max_pair_degree` and `max_monomial_degree`
apart for the same reason.

## 2. They are common on the cryptanalytic systems and absent on the classical ones

| instance | mutant elements | batches with one | batches | largest gap | regressions | **after a mutant** | largest drop |
|---|---:|---:|---:|---:|---:|---:|---:|
| katsura-5 | 0 | 0 | 5 | 0 | 0 | 0 | 0 |
| Fukuoka III `n=10` | 65 | **1** | 6 | **3** | 1 | 1 | 2 |
| Fukuoka III `n=15` | 335 | **2** | 7 | **3** | 1 | 1 | 2 |
| Fukuoka VI `n=10`, as published | 0 | 0 | 7 | 0 | 0 | 0 | 0 |
| Fukuoka VI `n=10`, specialized | 0 | 0 | 8 | 0 | 0 | 0 | 0 |
| Poseidon `t=3`, as generated | **164** | 12 | 20 | 1 | **0** | **0** | 0 |
| Poseidon `t=3`, input pinned | 38 | 7 | 11 | 2 | 1 | 1 | 1 |
| Poseidon `t=2 R_F=4` | 80 | 17 | 22 | 2 | 2 | 2 | 1 |
| Poseidon `t=2 R_F=2 R_P=2` | 37 | 8 | 13 | 2 | 1 | 1 | 1 |
| Poseidon `t=2 R_F=2 R_P=0` | 8 | 5 | 9 | 2 | 2 | 2 | 1 |

Three things, and the third is the one that decides.

**They are common where the milestone cares and absent where it does not.** Every Poseidon instance
produces them, in 5 to 17 of its batches; both Fukuoka type III instances produce them in one or two
batches but in bulk — 65 and 335 elements — at a gap of **three**, so a degree-4 matrix yielded
degree-1 relations. katsura-5 produces none, and neither does Fukuoka type VI in either form, with
seven and eight batches to do it in.

**Every single degree regression in the corpus followed a batch that produced a mutant.** The
`regressions` and `after a mutant` columns are equal on all ten rows. So the mechanism of §3 is not
hypothetical: when the schedule goes back down, it is because a lower-degree relation created
lower-degree work, every time. The attribution column exists precisely so that this could have come
out otherwise, and it did not.

**And there are almost no such events: zero, one or two per computation**, against 5 to 22 batches.
The decisive row is Poseidon `t = 3` as generated: **164 mutants across 12 of its 20 batches, and
zero regressions.** Their gap is one degree, and their pairs never land below the degree already
being worked — so 164 mutants bought nothing at all in scheduling terms. Mutant *count* does not
predict scheduling opportunity, and on this corpus the opportunity is at most two events per run.


## 3. The structural answer: immediate priority is already the selection rule

This is the heart of M22-D, and it is an argument about `PairQueue` rather than a measurement.

`PairQueue::select_batch` takes **every pending pair of the lowest available degree**, and the lcm
degree is the primary key under every [`PairSchedule`](pair-scheduling.md). So when a batch at
degree `d` produces a relation of degree `e < d`:

1. the relation is appended to the basis immediately, in the same iteration;
2. its critical pairs against the whole existing basis are generated immediately, in the same
   iteration;
3. and the *next* `select_batch` takes the lowest pending degree — which is at most the lowest of
   those new pairs, and therefore below `d` if any of them is.

So the remaining pairs of degree `d` wait, and the mutant's pairs go first. **That is exactly the
"immediate priority for lower-degree relations" of the plan's §9.3, and it is the existing
selection rule rather than an addition to it.** The ordering is asserted on a live queue in
`test_a_lower_degree_pair_is_selected_before_the_current_degree_finishes` rather than inferred from
reading the selection code.

The measurement in §2 is what turns that argument into a finding: `degree_regressions` counts the
times the schedule really did go back down, and `regressions_after_mutants` attributes the ones that
followed a batch which produced a mutant. The attribution is separate because a regression can also
follow an ordinary batch — a new element of the batch's own degree can pair low with an old one —
and without separating them the mechanism could be credited with work it did not do.

## 4. What an actual mutant algorithm would have to add, and why it is not here

Granted that immediate priority is free, the forms of the idea that would do something *more* are:

**(a) Interrupt the current batch.** A mutant is only available to *later* batches: the matrix it
came out of was already built. A mode that stopped committing to the whole of degree `d` before
learning anything from it would let the mutant eliminate the rest of degree `d`'s pairs.

That is **batch capping**, and M22-A measured it: a fixed cap of 64 is 3.6x on Fukuoka type III
`n=10` and 2.2x at `n=15`, by reducing 55% and 47% fewer pairs — because candidates returned sooner
let Gebauer–Möller eliminate pairs the uncapped run had already committed to. So the lever exists,
it is already measured, and it is not specific to mutants: it applies to every candidate a batch
produces, at whatever degree.

**(b) Sakata–Takagi's MF4: an auxiliary basis of intermediate relations and degree-decreasing
phases.** This is the form that is genuinely new, and it is genuinely a different algorithm — it
keeps relations that are *not* basis elements and schedules phases that walk the degree downwards.
It is out of scope for M22 by §3 of the plan ("Keep M22 centered on F4 scheduling, Hilbert
modeling, and bounded mutant experiments"), and M22-C supplies a reason to be wary of it
independently: **abandoning the ascending-degree discipline on an inhomogeneous system is
catastrophic.** `HilbertSelection::Deferred` does exactly that — defers a degree's remainder and
moves up — and it is 214x slower on Poseidon `t=2 R_F=2 R_P=2` and crosses the column budget on
`t=2 R_F=4`, an instance the baseline finishes in 374 ms. A degree-decreasing phase structure is
not the same manoeuvre, but it is in the same family, and the measured cost of leaving the degree
order is the largest single penalty M22 found.

## 5. Decision

**No mutant mode is added.** The plan's §9 go/no-go: *"If meaningful mutant relations are rare, or
Zeebra already prioritizes them effectively, document the result and do not add a new algorithmic
mode."* Both halves hold, for different reasons:

| question | answer |
|---|---|
| Are lower-degree relations detected? | **Yes, and the detection is tested independently** — `candidates_below_batch_degree` against `batch_degree`, with the batch degree and the polynomial degree never conflated. |
| Are they common? | **Yes on the cryptanalytic systems** — 5 to 17 of every Poseidon run's batches, and 65 and 335 elements in one or two batches on the two Fukuoka type III instances. **None at all** on katsura-5 or on either form of Fukuoka type VI. |
| Does Zeebra already prioritize them? | **Yes, by construction and in measurement.** `select_batch` takes the lowest pending degree, so a mutant's pairs precede the remainder of the current degree; and *every* degree regression measured followed a batch that produced a mutant. |
| Is there an opportunity left? | **Almost none.** Zero to two regressions per computation, and the instance with the most mutants — 164 over 12 batches — has zero. Mutant count does not predict scheduling opportunity. |
| What would a real mutant algorithm add? | Interrupting the current batch, which **is** batch capping and is already measured at 3.6x by M22-A; or MF4's auxiliary basis and degree-decreasing phases, which are a different algorithm, out of scope by §3, and in the family of manoeuvre M22-C measured at 214x slower and at one instance going from solvable to infeasible. |

So M22-D's deliverable is the instrumentation and the measurement, and its conclusion is that the
benefit a mutant mechanism would provide is **already captured by degree-first selection**, with the
one adjacent lever already measured under another name. That is a null result with a mechanism, not
an absence of evidence.

The instrumentation stays: `mutant_elements`, `batches_with_mutants`, `max_mutant_degree_gap`,
`degree_regressions`, `regressions_after_mutants` and `max_degree_drop` are the numbers that would
have to change before this conclusion did, and a later milestone contemplating MF4 should look at
them first.


## 6. Reproducing

```sh
cargo run --release --example f4_degrees
cargo test --lib mutant
cargo test --lib test_a_lower_degree_pair
```
