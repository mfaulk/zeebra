# M23 — Cryptanalysis Scoreboard and Structural Attack Development

**Measured at:** publication bound `9c8b80d6`…`14baabac` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](research/external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

**Status:** complete
**Prerequisite:** M22, merged
**Research issues:** #65, #71, #73 (registry and schema), #77 (methodology), #78, #81 (full-width
generation and solving-degree), #79 (formulation comparison), #70, #80 (external coverage), #82,
#85 (resultants)

M23 changes the unit of progress. M17 through M22 measured *optimizations*: a strategy, a cap, an
ordering, each reported as a factor on an instance. That is the right unit for an engine and the
wrong unit for an attack, and it produced a backlog in which "3.6x faster on Fukuoka III `n=10`"
and "no result at `t = 16`" sit in the same document with nothing relating them. From here, every
algorithmic claim has to answer one of two questions with a reproducible measurement:

1. **What public problem can zeebra solve, and is that solve a reproduction or a first?**
2. **For a problem it cannot solve, where exactly does the computation stop, and which stage got
   cheaper?**

The deliverable is a versioned scoreboard that answers both without ever adding them together.

## 1. The external position, as of 2026-11-05

The three 2026 CICO targets are **solved, externally, and the program is closed.**

| target | reward | the program's own words |
|---|---|---|
| Poseidon-31 CICO, `R_F = 6`, `R_P = 6` | $6,000 | "Solution verified on 10 April 2026" |
| Poseidon-31 CICO, `R_F = 6`, `R_P = 8` | $10,000 | "Solution verified on 6 May 2026" |
| Poseidon-31 CICO, `R_F = 6`, `R_P = 10` | $15,000 | "Solution verified on 6 July 2026" |

with "THE PROGRAM IS FINISHED" on the page, and the separate Poseidon1 partial-collision prize
"PAUSED STARTING 1 AUG 2026 AoE" though it nominally runs to 2029-01-01.
Source: <https://www.poseidon-initiative.info/>, read 2026-11-05 and re-read 2026-11-08 with both
readings identical.

**Those three rewards were claimed and are not claimable.** The tiers sit inside a programme that
"runs till January 1st, 2027", but the CICO problem itself is `finished` in the sense
`docs/research/prize-ledger.md` §1 defines: the organizer declares it complete and every tier is
verified. The amounts above are historical record, which is why §1's position is a *reproduction*
and not an opportunity. Claimability for every programme this repository tracks — window, budget,
verbatim status, read date — is `prize-ledger.md` §2, and no reward figure belongs in this document
without them.

Two consequences, and they are the reason this section is first.

**The best available outcome on those three rows is a reproduction.** A verified witness would be a
genuine result — it would be the first time this project solved a real challenge instance — and it
would not be a first solution of anything. [`Significance`] computes that distinction from the
registry rather than leaving it to a sentence in a report, and the three variants it can return for
an official row are `Reproduction`, `NoPublicSolutionRecorded` and `NoWitness`.

**A substantially different or cheaper attack is still a contribution.** The initiative's own
Gröbner Basis Exploratory program asks for exactly the pipeline this project has been building
since M17: construct a DRL/grevlex basis for feasible reduced-round Poseidon, try other monomial
orders, convert to lex, recover roots by univariate factorization, and **measure each stage's cost
and memory separately** so the complexity can be extrapolated. That stage-separated measurement is
the organizing principle of the scoreboard's metrics (§4.3), because it is the thing this
repository is in a position to do well and the thing a bounty table does not record.

## 2. What is in reach, stated before anything is run

M21 and M22 put the Poseidon frontier at **nine variables**: `t = 2, R_F = 4, R_P = 0`, 356 ms, and
the same nine variables at `t = 3` crossing a 60,000-column budget at degree 11 unless one free
input is pinned. The official instance is **118 variables** and the *smallest* row of a faithful
full-width ladder is **46**.

So the honest prediction for M23-B is that most full-width rows do not finish, and the milestone is
designed around that rather than against it: the deliverable is a stage-resolved measurement of
*where* each one stops, which is a result the plan's §B metrics are built to carry. What would make
the milestone a failure is not an unsolved row — it is an unsolved row reported without saying which
resource bound it hit at which degree, or a solved row that quietly changed the problem.

Three ways of quietly changing the problem are already known and are each blocked by a type:

- **Reducing the width** is a surrogate, not a reduction — `BenchmarkClass::Engineering`.
- **Planting the target** makes a solution exist by construction — recorded in the identity digest
  as `CicoTarget::PlantedFrom`, so a planted row cannot be mistaken for a stated-target one.
- **Relaxing the verifier** to the bounty's low-bit match is not a polynomial condition at all
  (`docs/research/poseidon.md` §3) and has no registered objective; `Objective::CicoExact` is the
  only CICO objective that exists, and adding a relaxed one would change every digest that used it.

## 3. The three benchmark classes

Never combined into one score, and never into one column.

| class | what a verified witness means | example |
|---|---|---|
| `Official` | a witness for the public challenge | `poseidon31-cico-rf6-rp8` |
| `FaithfulReduction { of }` | a witness for a genuinely easier problem, which says **nothing** about `of` | `poseidon31-cico-t16-rf2-rp0` |
| `Engineering { why }` | evidence about the implementation | `poseidon-t2-rf4-rp0-planted` |

A faithful reduction keeps the field, the state width, `k`, the stated constants and the exact
objective, and changes only the round counts. That is the strongest kind of reduction available:
the round constants are regenerated from `(prime bits, alpha, t, R_F, R_P)` by the same Grain LFSR,
so a reduced row's constants differ from the official row's — which is part of its identity rather
than a defect, and is why every ladder row has its own digest.

An engineering surrogate is not second-class work; it is differently-quoted work. M22's 1.67x from
`last-round-first` variable ordering was measured on `t = 2` surrogates and is a real measurement
about F4. It is not evidence about `t = 16`, and §6's workstreams exist to find out whether it
transfers.

## 4. The scoreboard

### 4.1 Identity

Three separate things, deliberately not merged:

| | what it pins | where |
|---|---|---|
| `ChallengeManifest::digest` | the **problem** — family, objective tag, parameters, target | `src/grobner/research/challenge.rs` |
| `ChallengeManifest::derived_digest` | the **generator** — round constants and MDS matrix | same |
| `InstanceManifest::provenance.sha256` | the **bytes**, for a problem that is a file | `research/manifest.rs` |

The identity digest covers the mathematics and excludes the paperwork: a corrected URL, a paid
bounty, an improved verifier sentence and a changed external status all leave it alone. An identity
that moved when a program updated its page would break every historical comparison keyed on it, and
the comparison tool's one job is to refuse to compare two runs whose digests differ.

The derived digest is separate because a parameter checksum cannot catch a changed generator. If
the LFSR's bit layout, its rejection sampling or the Cauchy construction changed, every registered
instance would become a different permutation with an unchanged identity. Three derived digests are
pinned in `test_the_derived_constants_are_pinned` for that reason.

### 4.2 The frozen registry

Twenty-two problems, frozen before the benchmark ran — and three more added in M23-D, which the
freeze test caught as an addition rather than a redefinition. `test_the_registry_is_frozen` pins
every id and digest, so redefining a row fails a test; adding one is a deliberate edit.

| id | class | vars | eqs | external status |
|---|---|---:|---:|---|
| `poseidon31-cico-rf6-rp6` | official | 116 | 104 | solved externally 2026-04-10 |
| `poseidon31-cico-rf6-rp8` | official | 118 | 106 | solved externally 2026-05-06 |
| `poseidon31-cico-rf6-rp10` | official | 120 | 108 | solved externally 2026-07-06 |
| `poseidon31-cico-t16-rf2-rp0` | reduction | 46 | 34 | — |
| `poseidon31-cico-t16-rf2-rp2` | reduction | 48 | 36 | — |
| `poseidon31-cico-t16-rf2-rp4` | reduction | 50 | 38 | — |
| `poseidon31-cico-t16-rf4-rp0` | reduction | 78 | 66 | — |
| `poseidon31-cico-t16-rf4-rp2` | reduction | 80 | 68 | — |
| `poseidon31-cico-t16-rf4-rp4` | reduction | 82 | 70 | — |
| `poseidon31-cico-t16-rf6-rp0` | reduction | 110 | 98 | — |
| `poseidon31-cico-t16-rf6-rp2` | reduction | 112 | 100 | — |
| `poseidon31-cico-t16-rf6-rp4` | reduction | 114 | 102 | — |
| `poseidon-t2-rf2-rp0-planted` | engineering | 5 | 5 | — |
| `poseidon-t2-rf2-rp2-planted` | engineering | 7 | 7 | — |
| `poseidon-t2-rf4-rp0-planted` | engineering | 9 | 9 | — |
| `poseidon-t3-rf2-rp1-planted` | engineering | 9 | 8 | — |
| `fukuoka-mq-III-n10-seed0` | official | 10 | 20 | published with answer |
| `fukuoka-mq-III-n15-seed0` | official | 15 | 30 | published with answer |
| `fukuoka-mq-III-n20-seed0` | official | 20 | 40 | published with answer |
| `fukuoka-mq-VI-n10-seed0` | official | 10 | 7 | published with answer |
| `fukuoka-mq-VI-n15-seed0` | official | 15 | 10 | published with answer |
| `fukuoka-mq-III-n34-seed0` | official | 34 | 68 | solved externally, 2015-08-04 |
| `fukuoka-mq-VI-n24-seed0` | official | 24 | 16 | solved externally, 2015-04-01 |
| `fukuoka-mq-V-n24-seed0` | official | 24 | 16 | solved externally, 2015-04-03 |

`N − E = t − 2k = 12` on every Poseidon row with `k = 2`, whatever the rounds — the underdetermined
direction M22-E found to matter more than state width does not shrink along the ladder, which is
why §6's M23-B benchmarks slices as well as the unspecialized system.

M23-D added `poseidon256-cico-2025-rf6-rp11`, `poseidon256-cico-2025-rf6-rp16` and
`poseidon64-cico-2025-rf6-rp13`: three tiers of the initiative's **2025** program that it still
lists as unsolved. Their objective constrains the *trailing* words rather than the leading ones —
`Perm(X1,...,X14,0,0) = (Y1,...,Y14,0,0)` — which is a different ideal and not a relabelling, so
`Objective::CicoExactTrailing` names it and nothing generates it. They are the only rows in the
registry with no public solution recorded, and both `cico_instance` and `dispatch_cico` refuse them
by name. See `docs/research/poseidon.md` §5a.

`fukuoka-mq-III-n34-seed0` is registered and deliberately not implemented: its file checksum is
empty because this repository does not hold those bytes, and its purpose is to keep the distance
between a toy example and the real challenge visible in the same table. It read `n = 55` until
#501, which is type I's lower bound and not a size type III offers at all — type III publishes
`n = 34..=53`. Correcting it also corrected its status: the hall of fame records `n = 34` seeds 0
and 1, so the row is `solved externally` (32 days 18 h of four Opterons, by XL with block
Wiedemann) rather than open, and the smallest type III size with *no* recorded solve is `n = 39`.

M27-B (#454) added `fukuoka-mq-VI-n24-seed0`, and it is the **first row in this family that is not a
toy example**. Type VI publishes `m = 16..=35` and the generator truncates `n = m * 1.5`, so `m = 16`
is `n = 24`; `SUPPORTED_DIMENSIONS` reaches `[10, 15, 20, 24]` and the row's checksum names real
challenge bytes. Its status is `solved externally` rather than `none recorded` — the hall of fame
records this exact instance as Faugère's 2015 F5-FGb submission, 5 280 s — so a witness here would
be a reproduction, which is the weaker and the honest reading. One diagnostic slice stops on
live-entry growth at degree 6; `docs/research/fukuoka-mq.md` §4.4 has the figures and the slice
policy.

M27 (#510) added `fukuoka-mq-V-n24-seed0`: the **same `n = 24`, over GF(2^8)**. `m = 16` is `n = 24`
in both signature families, so no new dimension was needed — what was needed was a runner that is
not hardwired to GF(31), since `type Q` and every MQ visitor in `examples/scoreboard.rs` were
written against `PrimeFieldElement64<31>` while the importer had handled the challenge's GF(2^8)
since #414/#415. The visitors are generic over the coefficient type now and dispatch on
`MqInstance::field`, and `ChallengeParameters::MqSystem`'s `field` is per row rather than the
constant `"GF(31)"` it was at every call site — it is in the identity digest, so that constant
would have made the first GF(2^8) row a GF(31) row carrying type V's `kind`. Both slices
re-measured at one commit stop identically at degree 6 on the same 13 602 x 19 132 matrix, and the
wall is 42.1 s against 105.1 s: **2.49x for the field alone**, with the computation held fixed.
`docs/research/fukuoka-mq.md` §4.5.

Two families are registered as `Official` with very different difficulty, and the status column is
what separates them: the Fukuoka toy examples are published *with* their answers so an
implementation can check itself, which makes a witness there a reproduction and not a result about
the challenge. "Official" means externally specified and unmodified. It does not mean hard.

### 4.3 Metrics, in four groups that are reported separately

**A. Verified attack frontier.** The hardest exact instance with an independently verified witness;
the maximum solved `(R_F, R_P)` within one family and objective; the largest public MQ `n` at a
stated field, type and seed; time and peak memory to that witness. A Poseidon result is quoted as
the full tuple `(p, alpha, t, k, R_F, R_P, objective, target)` — never as a round count, because two
configurations with the same round count can differ in everything else.

**B. Gröbner-basis frontier,** for a problem with no witness: highest completed pair-selection
degree, maximum Macaulay dimensions, peak live nonzeros and bytes, pairs processed, basis elements
generated, whether the basis completed, and `D` if established. The completed degree is a
**diagnostic, not a percentage**: reaching a higher degree does not imply less work remains. Every
incomplete run reports the limiting resource and the last fully completed stage.

**C. Full-pipeline cost, per stage** — generation, F4, FGLM, univariate solving, verification —
because M20 measured that on a wide field the cost is not in the matrices, and a single total would
hide exactly the stage the EF program asks about.

**D. Quality of the experiment.** Which of: a verified witness for the public objective; a completed
and independently checked basis; a validated reduced-round result; a successful specialization; an
unfinished run stopped by a resource limit; a planted or relaxed demonstration. A specialization
campaign additionally reports slices tried, slices that yielded a witness, and **total work
including the failures** — a fast successful slice is misleading if its success probability is low.

### 4.4 Layout

```text
research/scoreboard/
  challenges/           the registry, emitted from code so it cannot drift
  runs/                 one JSON record per run, named by problem, formulation and commit
  results/best.json     the fastest verified witness per problem
  results/history.json  accumulated across runs and milestones
  SCOREBOARD.md         generated
tools/
  scoreboard.sh         the measurement protocol: private target dir, pinned cores, a tier
```

`research/instances/` stays gitignored and un-redistributed; `research/scoreboard/` is committed,
because a scoreboard nobody can read from the repository is not one.

**The renderer and the comparison are in the crate, not in a separate script, and this is a
deliberate departure from the plan's Python tool.** The one rule this machinery exists to enforce
is "these two runs are of the same mathematical problem"; a second implementation of it in another
language would be a second place for it to be wrong, and it would not be covered by the test suite.
What stays in `tools/` is the part that is genuinely not the crate's business: the private target
directory, the core pinning, and the tier selection. The committed JSON remains the machine-readable
interface for anyone else's tooling, and `Json::parse` round-trips it (asserted) so the history can
be accumulated rather than overwritten.

## 5. What was decided in M23-0

**Hand-written SHA-256 rather than a dependency** (`src/util/sha256.rs`, 90 lines plus FIPS 180-4
vectors). `Provenance::sha256` was previously a string a shell script computed and no Rust code
could check. A checksum nothing verifies is a comment.

**The registry is code, not data.** `registry()` returns typed manifests and every runner takes its
instance from there through `ChallengeManifest::cico_instance`, so there is no second copy of the
constants anywhere to drift. The JSON under `research/scoreboard/challenges/` is emitted from it.

**`dispatch_cico` bridges the const generic.** `CicoInstance::system::<N>()` needs `N` at compile
time and the registry has fifteen distinct `N`, so a visitor takes the system at its own dimension —
the same shape as `MqVisitor`. The dimensions compiled are exactly the registered ones.

**Significance is computed, not written.** `ChallengeManifest::significance(verified)` returns one of
five variants from the class and the external status. `NoPublicSolutionRecorded` says in its own
`Display` that it is not a priority claim.

## 5a. What was decided in M23-A

**A run references its problem by digest, and a stale identity is refused.** `Scoreboard::add`
looks the problem up in the registry and compares digests; a mismatch is
`ScoreboardError::StaleIdentity` rather than a row in a table. The same check runs again on the way
out in `to_json`, so an emitted file cannot carry an identity the registry no longer describes.
`Comparison::of` refuses two different digests outright — and it does **not** compare ids, because
two runs can agree on a name and disagree on what it means.

**Unfinished runs are not ranked.** `Scoreboard::best` returns verified witnesses only. Ranking two
crossed budgets against each other would assert that a higher degree is nearer a solution, which is
false; those rows go to a separate table whose heading says it is a diagnostic. This is the plan's
§4.3B rule, enforced by the type rather than by the prose around it.

**The ±20% band is in the code.** `Comparison::runtime_readable` is false inside it. A difference
that cannot be read is still reported — with that flag — rather than quoted or dropped.

**Stages are measured by running the pipeline in stages.** The runner calls `f4_reported`, then
`fglm_to_lex_with_options`, then `solve_from_lex_basis`, each timed, rather than going through
`solve_one_planned`. That is what makes a per-stage table possible at all; the cost is that the
planner's route choice is not exercised there, which `solve_baseline` and `cryptanalysis_ladder`
still cover.

**A campaign reports its failures.** `Campaign::work_per_witness` is the whole campaign's time over
the witnesses — as two integers, since a record holds no floats — and is `None` when there were
none, where a division would produce an infinity presented as a measurement. The success rate
carries a 95% Wilson interval in basis points: at 1 witness in 20 slices that is 0.89% to 23.6%,
where the normal approximation's lower bound is negative and therefore not a probability.

**`Json` gained a parser.** The history file is read, extended and written back, and a writer with
no reader would mean either losing every earlier milestone's results on each run or carrying a
dependency to read back what eighty lines wrote. Floats are rejected rather than accepted and
truncated, which keeps the no-float invariant on the way in as well as out.

## 5b. The milestone report

### 5b.1 What public problem can zeebra solve?

Three answers, at three levels of fidelity, and the scoreboard keeps them apart.

| class | hardest solved | evidence |
|---|---|---|
| official | Fukuoka MQ type III `n = 15` | the published answer, recovered without being given it, `D = 1`, 7.9 s |
| faithful reduction | Poseidon-31 CICO at **`t = 16`**, `R_F = 2`, `R_P = 0`, sliced | 3 witnesses in 8 precommitted slices, each checked by running the permutation |
| engineering surrogate | `t = 2`, `R_F = 4`, planted | 371 ms |

**The `t = 16` witness is the milestone's result.** It is a 14-word input whose first two words are
the challenge's own `0xc09de4, 0xee6282` and for which `permutation_plus_linear` returns zero in the
first two output words, exactly, over KoalaBear at the official state width with the official
objective. `Significance` reports it as `ReducedInstanceWitness { of: "poseidon31-cico-rf6-rp8" }`:
a real result about a genuinely easier problem, and not evidence about any official target.

Is it a reproduction or a first? Neither — it is a witness for a *reduction*, which is a third
thing, and the type says so rather than leaving it to a sentence. The three official CICO targets
were solved externally in 2026; the strongest claim available on them is a reproduction, and zeebra
has not produced one.

### 5b.2 Where does the computation stop, and which stage got cheaper?

**Nothing got cheaper.** M23 added no optimization, and the three formulations it compared are all
*slower* than the generated layout at full width. What it produced instead is the first map of where
the wall is:

| | small instances (M21/M22) | full width (M23-B) |
|---|---|---|
| bound that binds | columns, 60 000 | **live entries, 20 000 000** |
| degree at the stop | 11 | **4 to 6** |
| direction of difficulty | the underdetermined surplus | the state width itself |

Fourteen of eighteen full-width rows cross the entry cap at degree 4 or 5. The degree reached
*falls* as the instance widens. So the obstacle at `t = 16` is matrix **density early**, not support
growth late, and a strategy aimed at the column count is aimed at a bound that no longer binds
first. Every M22 workstream — pair order, batch caps, Hilbert-driven selection — was aimed at
exactly that bound.

And the stage split is unambiguous on every instance that finishes: F4 is 99.5% of the full-width
run, the conversion 0.12 s at `D = 81`, the univariate search 0.02 s, the verification 4 µs. On
Fukuoka `n = 15` it is 7 873 ms of F4 against 0.1 ms of conversion. That answers the EF program's
stage question for these instances: over a 31-bit field with a small quotient dimension, there is
nothing outside F4 worth optimizing. It is also the reverse of M20's finding over a 254-bit field,
where root-finding dominated — so "which stage dominates" is a property of the instance and the
field, not of the pipeline.

### 5b.3 What M23 corrects

**M22-E's variable-ordering result does not transfer.** `last-round-first` was 1.67x faster on the
`t = 2` surrogates and is **0.42x** at `t = 16` — 2.4x slower, with 2.5x the peak memory. The
mechanism is unchanged; what changed is that the first round introduces sixteen variables rather
than two, so there is no small block to front-load. This is the clearest vindication of the
milestone's premise: an optimization validated on a surrogate was not evidence about the real
width, and only measuring against a registered full-width problem showed it.

**A campaign over trials that never finished has no success rate.** The first type VI `n = 15`
campaign printed "0 witnesses in 8 slices; success rate 0.00% to 32.44%" when all eight slices had
crossed the entry cap. That is a claim about the instance from trials that tested the budget.
`Campaign::stopped`, `decided()` and a `None` interval now make it impossible to state.

**An affine elimination can cost more than it saves.** Projecting the full-width slice to 32
variables makes F4 1.16x faster and the run 1.5x slower, because the sweep itself takes 19.95 s
against the 4.2 s it saves. At `t = 2` the sweep was microseconds and nobody had measured it.

### 5b.4 Which bottleneck most limits further progress

**The Macaulay matrix's density at degree 4–5 in the S-box-per-variable formulation**, and the
formulation is the part worth attacking.

The evidence that it is the formulation rather than the engine is M23-E: on the *same* registered
slice, eliminating the 32 S-box variables by straight-line evaluation and taking one resultant
solves in **52 ms** what F4 takes **30 142 ms** to solve — a 578x difference — and returns all
three base-field witnesses where F4 returns the first. The S-box-per-variable formulation exists to
hold the degree at 3 and pays 32 variables for it; when only two inputs are free, those variables
are the whole cost and the degree it avoids (`3^rounds`) is affordable.

That bounds where to look next in both directions:

- **Not** in F4's scheduling. M22 measured 7%–14.5% on structural counters there, and M23-B shows
  the binding bound is a different one.
- **In the formulation**, where the measured factor is nearly three orders of magnitude on the
  instance shape that matters. The resultant route does **not** reach further than F4 — both stop at
  two rounds — but its limit is arithmetic and written down (`16 · 3^{5·rounds}` field operations)
  where F4's is a matrix nobody can bound in advance. A cost difference of 578x at the shared
  frontier is the finding; an extension of the frontier is not.

  > **Superseded, 2026-11-05.** "Both stop at two rounds" and "an extension of the frontier is not"
  > were true of the implementation M23-E measured and are now false. The binding cost there was
  > `lagrange_interpolate` at `O(n³)` — the third bullet below — and #162 stage 1 made it `O(n²)`.
  > With that one change the four-round rows finish, and the registered reductions
  > `poseidon31-cico-t16-rf2-rp2` and `-rf4-rp0` now carry **verified witnesses** at 47.6 s and
  > 50.6 s, checked through `permutation_plus_linear` by `CicoInstance::is_solution`. F4 still stops
  > at two rounds on the same slices, so **the resultant route does now reach further, and this is an
  > extension of the verified attack frontier** — from two rounds to four, on faithful reduced-round
  > instances. The two-round row also improved 8.65x, from 51.9 ms to 6.0 ms.
  >
  > Three things this does *not* change. It says nothing about the official `R_F = 6` targets, whose
  > own disclosed solutions cost 7 h on 96 GPUs and 1 d 17 h on 128 CPU cores. The `16 · 3^{5·rounds}`
  > bound still holds and still rules out six rounds. And the credit belongs to the interpolation
  > fix, not to the subgroup-NTT route that was built to attack the same stage — that route measures
  > **1.19–1.20x slower**, because a power-of-two domain pads 13 123 samples to 16 384 and the
  > determinants are 98.9% of the row. See [`research/resultant-elimination.md`](research/resultant-elimination.md)
  > §6, whose §6.4 records that determinant work is `d^5` against a quadratic interpolation's `d^4`,
  > so no further interpolation improvement can matter for this route.
- **And, unexpectedly, in `lagrange_interpolate`**, which M23-E measured at `O(n³)`: 7.4x–7.9x per
  doubling of the point count, 12.9 s at 2 000 points, extrapolating to about an hour at the 13 123
  the four-round row needs — against a few minutes for all of that row's determinants together.
  **Fixed: #162 stage 1 made it `O(n²)` (measured exponent 1.86–2.12), and those 13 123 points now
  interpolate in 1.37 s rather than an extrapolated hour. That is what moved the frontier above.**
  The figures in this bullet are the pre-#162 measurement and are kept as the one that found the
  defect.
  Attempting a row that does not finish is what found it, and it reordered the spike's own list of
  what to fix.

### 5b.5 The same instances across three milestones

Historical results are preserved rather than overwritten — `results/history.json` is appended, never
rewritten from loaded records — so the same problem can be followed across milestones. Two views,
kept apart because they answer different questions.

**Identical instances, same configuration.** This is the regression view, and it should be flat:

| instance | M21 | M22 | M23 |
|---|---|---|---|
| Fukuoka III `n=10` | 111 ms | 118.6 ms uncapped, **32.7 ms** at a 64-pair cap | 114 ms |
| Poseidon `t=2 R_F=4` surrogate | 371 ms | 351.9 ms, **218.7 ms** last-round-first | 371 ms |
| Poseidon `t=3 R_F=2 R_P=1` | column budget at 18 167 ms | 18 167 ms, 42 229 columns | 17 091 ms, 42 229 columns |

It is flat, which is what it should be: M23 added no optimization. The one thing this view shows is
that **the scoreboard's figures are the default configuration's** — M22's 3.6x on Fukuoka `n = 10`
came from a 64-pair batch cap that M22 deliberately did not make the default, so the scoreboard
reproduces M21's number and not M22's best. A scoreboard that quoted the best configuration per row
would not describe what the library does.

**Advance to harder instances.** This is the frontier view:

| problem | M21 | M22 | M23 |
|---|---|---|---|
| Fukuoka III `n=15` | not established | basis computed, 3 829 ms capped | **verified witness, and it is the published answer**, 7 874 ms |
| Fukuoka III `n=20` | — | — | stopped at the entry cap, degree 5 |
| Fukuoka VI `n=10` | dead slices measured | witnesses on two slices | **6 witnesses in 8 slices**, 0.8 s per witness, rate 40.9%–92.9% |
| Fukuoka VI `n=15` | — | — | eight slices, **no verdict**: all crossed the entry cap at degree 9 |
| Poseidon `t = 16`, any rounds | no attempt | not the main benchmark | **verified witness** at `R_F=2, R_P=0` sliced; an eighteen-row ladder with every stop named |
| a non-Gröbner elimination | — | deferred | a resultant, **578x** faster on the same slice |

### 5b.6 One deviation from the plan, with its reason

The plan asked for content hashes of "any equivalent transformed representation". M23 records a
transformation by **name and seed** — `slice(12 fixed, seed 1) + last-round-first` — and not by a
digest of the transformed system. A digest would pin *which* system was measured, which the name
and the seed already do (`Specialization::seeded` promises the slice reconstructs); what it would
not do is establish equivalence, since two presentations of one ideal have different digests by
construction. The equivalence evidence used instead is stronger: all four formulations of the
full-width slice report the same quotient dimension `D = 81` — an invariant no relabelling or affine
projection can move — and each recovers a witness that passes the permutation check after its own
inverse is applied.

### 5b.7 What M23 does not claim

- No official target was solved, and the three CICO targets were solved externally by other attacks
  in 2026. Nothing here is a step toward them that can be quantified as a fraction.
- The full-width witness is at `R_F = 2, R_P = 0` against an official `R_F = 6, R_P ∈ {6, 8, 10}`.
  The 2025 program's tiers at comparable round counts — over a *different* objective — were claimed
  by others in 2024 and 2025, which says those round counts are reachable by some attack and not by
  this one.
- Every figure comes from one machine under a stated budget, and runtime differences inside ±20%
  are not read.
- The scoreboard's numbers are the **default** configuration's. M22 measured a 64-pair batch cap at
  3.6x on Fukuoka III `n = 10` and deliberately did not make it the default; the scoreboard
  therefore reproduces M21's 114 ms rather than M22's 32.7 ms on that row. A scoreboard that quoted
  the best configuration per row would not describe what the library does.

## 6. Sub-milestones

| phase | workstream | deliverable |
|---|---|---|
| M23-0 | challenge registry | frozen official targets, ladder, surrogates and MQ rows, with digests |
| M23-A | scoreboard infrastructure | run records, aggregation, generated Markdown, a comparison that refuses mismatched digests |
| M23-B | full-width Poseidon ladder | `t = 16` rows measured against the exact objective under a fixed budget |
| M23-C | structural reformulation | two equivalent formulations of one full-width row, compared and inverted |
| M23-D | external benchmark expansion | Fukuoka III `n=15` witness, VI `n=15` campaign, one historical EF target |
| M23-E | resultant feasibility | a bounded spike on one small instance, with the negative result recorded if that is the result |
| M23-I | integration | scoreboard with history, M21/M22/M23 comparison, milestone report |

### What each one produced

| phase | PR | outcome |
|---|---|---|
| M23-0 | #143 | 22 problems frozen with digests; SHA-256 hand-written; `Significance` computed |
| M23-A | #145 | run records, three refusals, stage-split costs, campaign statistics, a JSON reader |
| M23-B | #152 | eighteen full-width rows; **a verified witness at `t = 16`**; the binding bound moves to live entries |
| M23-C | #152 | four formulations compared; M22-E's winner is 2.4x **worse** at full width |
| M23-D | #153 | Fukuoka `n = 15` recovers the published answer; three open 2025 tiers registered; the campaign-rate correction |
| M23-E | #157 | a resultant solves the same slice **578x** faster than F4, and reaches no further |
| M23-I | #158 | the scoreboard, the history, and §5b's report |

### Acceptance criteria

**M23-0.** Every registered instance has a stable id, a parameter digest, an exact objective and an
independent verifier; every Poseidon row builds and its S-box equations vanish at a real trace;
every planted row's recorded plant solves it; the ladder is frozen by a test before it is run.

**M23-A.** Two runs of the same instance on different commits compare automatically, and a
comparison across different digests is refused rather than rendered. The renderer needs no
dependency beyond the Python standard library. Classes are never summed.

**M23-B.** The scoreboard contains full-width rows with reproducible outcomes, verified witnesses
for any that succeed, and for the rest the limiting resource, the degree reached, and the matrix
dimensions at that degree. Slices use precommitted seeds; planted slices appear only as controls.

**M23-C.** At least two mathematically equivalent formulations of one genuine full-width
reduced-round row are compared under one budget, with the transformation inverted and any recovered
witness re-verified through the permutation. A reduced variable count alone is not accepted as an
improvement.

**M23-D.** At least two externally defined families, and a validation target strictly harder than
anything M21 completed.

**M23-E.** A resultant's actual degree against the Bézout bound on one controlled instance, with
candidates verified through the original permutation and total work compared against F4 on the same
problem — or a documented reason to defer.

**M23-I.** A generated scoreboard with immutable identifiers and history; stage-separated F4, FGLM,
root-solving and verification figures wherever those stages are reached; and a report naming the
bottleneck that most limits further progress.

## 7. Execution and measurement policy

Three tiers, because a scoreboard that runs everything on every pull request stops being run:

| tier | when | what |
|---|---|---|
| correctness smoke | every pull request | generators, verifiers, transformations, the registry's freeze tests, the small rows |
| stable suite | on `main` and on demand | runtime and memory across commits, on one machine with a stated affinity policy |
| frontier | on demand | larger budgets, new full-width or larger MQ attempts |

**The stable suite does not run on CI, and that is deliberate.** Every figure in these documents
comes from one workstation, pinned, under a stated budget; a GitHub-hosted runner's timings are not
comparable with them, so a scheduled job there would produce numbers that could not be put in the
same table. CI runs the correctness smoke tier — which asserts outcomes, not durations — and the
stable and frontier tiers are run by hand on the designated machine through
`tools/scoreboard.sh`, whose records carry the machine, the build and the affinity so a reader can
see which runs are comparable. `workflow_dispatch` is available for a branch that wants the smoke
tier on demand.

Performance comparisons state the machine, the compiler flags and the core-affinity policy, and
follow the A/B discipline M19 settled on: two binaries from one tree, interleaved, pinned. This
machine's run-to-run variation is about 6%, and M22 declined to read runtime differences inside
a ±20% band; M23 keeps that rule.

Resource limits are column- and byte-bounded rather than time-bounded, so a failure is reproducible
rather than "it took too long on this machine". The limits F4 enforces internally are not an
operating-system ceiling, so a frontier run is additionally supervised externally for wall clock and
process memory.

## 8. Risks

| risk | response |
|---|---|
| every full-width row fails and the milestone looks empty | §4.3's group B is the deliverable for a failed row; the report's job is to name the bottleneck, not to find a win |
| a surrogate's result is quoted as progress on a challenge | `BenchmarkClass` is in the identity of every row and `Significance` is computed from it |
| the ladder is chosen to flatter the result | frozen in M23-0, pinned by a test, before M23-B runs |
| a reformulation changes the problem | every transformation is invertible and the recovered witness is re-verified through the permutation, which no generator bug can make pass |
| the comparison silently compares different problems | the digest is checked first and a mismatch is an error |
| round constants change under us | `derived_digest`, pinned |

## 9. Definition of done

- A generated scoreboard with immutable problem identifiers and historical results.
- All three official Poseidon-31 CICO targets registered and independently checkable.
- A full-width reduced-round ladder attempted under controlled budgets.
- At least one full-width structural transformation validated and measured.
- A harder Fukuoka MQ benchmark investigated, with its outcome documented either way.
- Separate F4, FGLM, root-solving and verification figures wherever reached.
- A comparison against a fundamentally different elimination method, or a documented deferral.
- A report naming the bottleneck that most limits further progress.

No part of this is met by weakening a problem, silently changing a constraint, or omitting a failed
run.

## 9a. Definition of done, item by item

| item | status |
|---|---|
| a generated scoreboard with immutable identifiers and historical results | **met** — `research/scoreboard/`, rendered from the accumulated history |
| all three official CICO targets registered and independently checkable | **met** — and their external status recorded with dates |
| a full-width reduced-round ladder attempted under controlled budgets | **met** — eighteen rows, every stop a reproducible resource bound |
| at least one full-width structural transformation validated and measured | **met** — four formulations, same `D`, same witness, measured apart |
| a harder Fukuoka benchmark investigated, outcome documented either way | **met** — III `n = 15` solved to the published answer, III `n = 20` out of reach, VI `n = 15` undecided, VI `n = 10` measured at 0.8 s per witness |
| separate F4, FGLM, root-solving and verification figures wherever reached | **met** — every run record carries the stage split |
| a comparison against a fundamentally different elimination method | **met** — M23-E, 578x on the same slice |
| a report naming the bottleneck that most limits further progress | **met** — §5b.4 |

Two things the milestone did **not** do, stated rather than omitted:

- **No optimization.** Nothing here made any instance faster. The three formulations compared are
  all slower than the generated layout at full width, and the one route that is dramatically faster
  — the resultant — is an elimination method rather than an improvement to the engine.
- **No official target.** The hardest official problem solved is a Fukuoka toy example published
  with its answer. The `t = 16` witness is for a registered reduction.

## 10. Reproducing

```sh
cargo test --lib grobner::research::challenge   # the registry's freeze and faithfulness tests
cargo test --lib grobner::research::scoreboard  # the refusals: stale identity, different problems
cargo test --lib grobner::research::record      # the JSON round trip
cargo test --lib util::sha256                   # FIPS 180-4 vectors

tools/fetch-mq-challenge.sh                     # for the MQ rows
tools/scoreboard.sh                             # smoke tier, writes nothing
tools/scoreboard.sh stable --write              # regenerates research/scoreboard/
```

Set `CARGO_TARGET_DIR` to a path inside the worktree for anything measured. The default target
directory is shared between worktrees of this repository and keyed by package and profile rather
than by checkout, so two checkouts overwrite each other's `libzeebra.rlib` — which surfaces as an
example failing to compile against exports that are plainly present. `tools/scoreboard.sh` sets it.

Later workstreams add their own commands to this section as they land.
