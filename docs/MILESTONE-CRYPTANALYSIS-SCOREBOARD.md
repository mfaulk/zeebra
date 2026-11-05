# M23 — Cryptanalysis Scoreboard and Structural Attack Development

**Status:** open (M23-0 merged)
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
Source: <https://www.poseidon-initiative.info/>, read 2026-11-05.

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

Twenty-two problems, frozen before the benchmark ran. `test_the_registry_is_frozen` pins every id
and digest, so redefining a row fails a test; adding one is a deliberate edit.

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
| `fukuoka-mq-III-n55-seed0` | official | 55 | 110 | none recorded, 2026-11-05 |

`N − E = t − 2k = 12` on every Poseidon row with `k = 2`, whatever the rounds — the underdetermined
direction M22-E found to matter more than state width does not shrink along the ladder, which is
why §6's M23-B benchmarks slices as well as the unspecialized system.

The last row is registered and deliberately not implemented. `SUPPORTED_DIMENSIONS` stops at 20,
its file checksum is empty because this repository does not hold those bytes, and its purpose is to
keep the distance between a toy example and the real challenge visible in the same table.

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
