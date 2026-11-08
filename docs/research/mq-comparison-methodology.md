# MQ solver comparison methodology, and the F4 baseline column

**Measured at:** not measured here — every figure is quoted from the record that produced it, and
cited there. §7's baseline table transcribes `research/scoreboard/runs/` and
[`fukuoka-mq.md`](fukuoka-mq.md) §4; the external figures in §6 are published attacks' own reported
times.

Deliverable for **#77 (B4)**, a child of epic #66. It defines the comparison **before** B1–B3 are
implemented, which is the issue's whole point: "whichever is implemented first will otherwise define
the benchmark in its own favour."

**What this document is, and is not.** It is not a proposal. Nearly every rule below is already
enforced in code, and this note's job is to say where, so the rules have one address. That address
was missing and the code noticed: `src/grobner/external/board.rs:329` declines to put a check in
`Environment` because "that type is shared with the cryptanalysis scoreboard, whose own
comparability rules are **#77's to change**" — a deferral to a document that did not exist. §9 lists
what is genuinely absent rather than merely undocumented.

## 1. The primary metric: time and peak bytes to a verified solution

**B1, B2 and B3 produce different objects** — a Gröbner basis, a solution found by enumeration, and
a kernel vector. Timing those against one another is not a comparison. The metric is therefore
anchored on the one statement all three genuinely answer:

> **given the system, produce a verified solution vector.**

Two consequences, both load-bearing:

- **A Gröbner basis is an intermediate result, not the deliverable.** An F4 figure must include FGLM
  and `solve_one`. `RunRecord::elapsed()` is the sum over *all* stages
  (`Generation`, `Grobner`, `Elimination`, `Conversion`, `Univariate`, `Verification`), so the
  headline number already has verification inside it — the committed `fukuoka-mq-III-n15-seed0`
  record is 7 873 596 977 ns over a `grobner` of 7 872 720 198, a `conversion` reporting `D = 1`,
  a `univariate`, and a **`verification` of 226 118 ns**.
- **Conversely, crossbred and XL never produce a basis**, so basis quality is not available as a
  comparison axis at all. It is not a secondary metric either (§2); it simply does not exist for two
  of the three candidates.

### 1.1 "Verified" means by an independent verifier, and a type enforces it

`Significance` is **computed from whether a witness passed independent verification**, never
asserted by a report. The gate is one line — `ChallengeManifest::significance` returns
`Significance::NoWitness` immediately unless `verified_witness` — and its only input is
`RunOutcome::is_verified_witness()`, which is true for exactly one of seven outcome variants. There
is no route by which a basis-only or limit-stopped run acquires a claim.

The rationale is worth quoting, because it is the reason the computation is not a convenience:

> Computed from the class and the external status rather than asserted by a report, which is the
> point: the distinction between reproducing a solved challenge and solving an open one is not
> something a summary should be free to phrase generously.

For MQ, verification is **substitution into the originally published system**, and it is total:
evaluate all `m` polynomials at the candidate and require every one to be zero. The verifier string
every Fukuoka manifest carries says so, and says what it refuses to trust:

> evaluate the imported coefficient vectors of the original published file at the candidate,
> inverting any specialization first

— the specialization inverse being necessary because a slice result is a result about the slice. A
witness lifts (the pinning forms `x_i - a_i` make a recovered point a point of the original
variety); an *empty* slice says nothing about the instance, which is why
`RunOutcome::SliceEstablishedNothing` exists as its own outcome.

A rejected candidate is also not an absence: `RunOutcome::WitnessRejected` is "a defect, not an
absence", and keeping it distinct is what stops a verification failure being reported as a
non-completion.

### 1.2 Peak bytes: which quantity, and the one that is missing

"Peak bytes" names two quantities that differ by **two orders of magnitude**, and the scoreboard
keeps them in separately-named fields for that reason: `peak_estimated_bytes` is live matrix entries
at 16 bytes apiece, `measured_peak_resident_bytes` is process `VmHWM` — 195 MB accounted inside a
14.75 GB process on Fukuoka III `n = 20` (#237). A reader must never be able to mistake one for the
other, and the naming is the mechanism.

`VmHWM` is a process high-water mark, so attribution is not free: a process that runs seven rows
reports one figure covering all seven, which is a *ceiling* over them rather than a measurement of
any one. `measured_peak_is_attributable()` requires `measured_peak_rows_in_process == Some(1)`.

**This is where the primary metric is currently half-populated, and §9 records it as a gap:** the
three rungs with a verified witness carry no measured peak at all, and the four rungs that do carry
`VmHWM` are all limit stops. So "time *and peak bytes* to a verified solution" has its time half on
three rungs and its measured-bytes half on none of them.

## 2. Secondary metrics, and what makes them non-comparable

Per-algorithm secondaries are worth recording because they *explain* the primary result, and are not
comparable across algorithms. `GrobnerFrontier` records max matrix rows and columns, max pair
degree, peak live nonzeros, pairs reduced, elements added and quotient dimension.

**The honest statement is that the type system enforces non-comparability across *environments* and
across *problems*, and not yet across *algorithms*.** What is enforced:

| mechanism | refuses | why, in its own words |
| --- | --- | --- |
| `Comparison::of` → `DifferentProblems` | identity digests differ | "The ids are not compared: two runs can agree on a name and disagree on what it means, which is the whole reason the digest exists" |
| `Comparison::of` → `DifferentConcurrency` | worker counts differ | "A parallel wall clock divided by a single-threaded one is a core count, not a solver speedup, and the ratio is the number a reader would quote" — refused rather than caveated |
| `ScoreboardError::StaleIdentity` | the problem was redefined after the run | "the measurement is about something the registry no longer describes" |
| `Environment::comparable` | machine, cpu or build differ | a caveat, not a refusal: "the comparison is still of the same quantity measured imperfectly" |
| `Comparison::of` caveat | either side lacks a verified witness | "the runtimes are costs of different things" |
| `runtime_readable` | a ratio inside ±20% | the project's noise band on this hardware; the comparison is still reported, with this `false` |
| `BenchmarkClass` | aggregating across classes | "a `t = 2` planted witness and a `t = 16` official witness are not summable in any direction" |
| `FigureBasis` | an estimate in a `measured_*` field | a `SchemaError`, not a caveat |

And what the module refuses to produce at all: **a single score**, and **a ranking of unfinished
runs** — "reaching a higher degree does not imply less work remains, so 'further' is not 'better'
and the type refuses to pretend otherwise."

**The gap, stated plainly.** A hypothetical XL row's "matrix columns" would render in the same column
as F4's Macaulay width with nothing in the type system saying they are different objects.
`FigureBasis` labels a figure's *basis*, not its *comparability scope*. Until a second algorithm
exists, the rule in this section is the only thing enforcing it, so it is written here rather than
left to the reader: **a secondary metric is comparable only within one algorithm, and a table that
places two algorithms' secondaries in one column is wrong even when both numbers are right.**

## 3. The instance ladder

The ladder for this comparison is the **Fukuoka MQ** one, from #70, because that is where published
external results exist. `fukuoka-mq.md` §4 presents it as five size steps, each with a stated
barrier, and `SUPPORTED_DIMENSIONS = [10, 15, 20, 24]` pins the frontier.

| rung | what it is for |
| --- | --- |
| type III `n = 10` | the published toy. Sanity in both directions — the system vanishes at the published answer *and* is solved to it. **"Not a competitive result and should not be quoted as one"**: 24 variables short of the smallest published type III challenge |
| type III `n = 15` | the largest toy that finishes under the standing budget |
| type III `n = 20` | the first that does not fit. A **documented resource stop**, not a failure |
| type VI `n = 10` | underdetermined, so sliced — and the size where the slices are *decided*, which makes a success rate meaningful |
| type VI `n = 15` | the same family where **no slice is decided**: the campaign "reached no verdict", which is not eight failures |
| type VI / V `m = 16` (`n = 24`) | the first *real* challenges. Imported and run; the solver stops at degree 6 |
| type III `n = 34` | registered and **deliberately not implemented**, "to show the gap in the family this crate has actually measured" |

### 3.1 Per-rung expectations are retrospective, and that is a gap

#77 asks for "an instance ladder with per-rung expectations", so that "the point where each algorithm
fails is itself a reportable result". The typed machinery for this exists — `Rung::{Easy,
Intermediate, Challenging}`, "a judgement about the rung's role in the ladder, not a measurement",
with `Challenging` defined as "expected to exhaust at least one engine's limits" — but **it carries
no Fukuoka rung**: `Rung` lives on the cross-library corpus ladder, and the challenge registry has
no difficulty label at all.

So §3's table is what was *observed*, not what was *expected in advance*, and an expectation stated
after the run cannot play the role #77 wants. Recorded as a gap in §9 rather than papered over by
back-dating labels onto measured outcomes.

## 4. Failures are data, and how they are encoded

A non-completion is a row, never a gap. `Limit` is "the plan's 'limiting resource and last fully
completed stage', as a type rather than as a sentence, **so a report cannot omit it**": the resource
that bound, the solver's own words, the pair degree reached, and the last stage that ran to
completion.

The rule, as a test's doc comment puts it: **"A missing row is a gap; a row naming a limit is a
result."** The renderer repeats it where a reader will see it — "A higher degree is **not** nearer a
solution: this table is a diagnostic, not a progress bar."

Four kinds of non-completion are kept distinct, and the distinctions are the methodology:

- **`StoppedByLimit`** — a resource stop. Preferred over a wall-clock stop where there is a choice,
  because "an entry count crosses at the same counter on any machine, so the ceiling can be written
  down, where a time stop would make it a fact about how busy the box was."
- **`WitnessRejected`** — #77's "incorrect result". A defect, not an absence.
- **`SliceEstablishedNothing`** — an empty slice. "A run that reported an empty slice as 'no
  base-field point' would be claiming the problem has no solution."
- **A campaign with no decided slice** — `success_rate_basis_points` returns `None` rather than zero,
  because "0 witnesses in 8 slices" for a campaign that decided nothing is a different statement
  from a rate of zero.

## 5. Build, hardware and protocol

Cited rather than restated, as #77 asks.

- **ISA floor**: `.cargo/config.toml` pins `-C target-cpu=x86-64-v3` — "`native` would make a build
  artifact depend on the machine that produced it". And `RUSTFLAGS` **replaces** rather than extends
  those flags, which has cost this repository three sets of figures; verify with
  `cargo build -v 2>&1 | grep target-cpu`.
- **Profile**: `Cargo.toml`'s `[profile.release]` at `lto = "fat"`, `codegen-units = 1`. `bench`
  inherits it; `ci-release` is explicitly *not* the measurement instrument.
- **Hardware**: `MILESTONE-COMPETITIVE-MQ-SOLVING.md` §7.1. Run-to-run noise band **~20%**;
  differences under it are not read.
- **Protocol**: §7.2, inherited and not weakenable. `tools/benchlock.sh` for every timing — "a figure
  taken without the lock is not publishable" — with `end=exited` rather than `status=0` as what
  asserts completion; `tools/rss-guard.sh` where allocation risk is material, where **exit 1 means
  nothing was guarded and that is not a pass**; never `taskset … timeout … <binary>`, which once
  produced a recorded instance wrong by ~7 000x.
- **Authorization**: §9. Any run projected past ~2 h wall or ~64 GB peak RSS needs an explicit owner
  decision, and §7 below records where that boundary — not capability — is why four rungs stop.

## 6. How published external results enter, and the two rules that keep them out of ratios

External figures **bound expectations and are not head-to-head measurements**. `ReferencePoint`
carries each with its conditions, and the type refuses a bare number:

> Every field that carries a figure carries its conditions beside it. **A time without its hardware
> and its software is not comparable to anything.**

`ExternalStatus` is dated, because "'unsolved' is a claim with a shelf life"; `DisclosedMethod` is
separate from it, because "a program can verify a submission without naming the submitter", and
`Unknown` is "the honest state for a solved problem with no technical report, and **not a synonym for
'brute force'**".

Two rules do the real work:

**No wall-clock speedup against an old published figure, anywhere.** The absolute form is stated for
Magma's 2004 page — the hardware is "twenty-two years old and the comparison is unnormalizable", so
"even where an instance matched, a wall-clock ratio would measure the machines". What *may* be
reported: invariants, and ratios **between systems under one implementation**. The Anemoi precedent
is why the rule is absolute: an apparent 507x advantage over published Magma was mostly Magma's
generic arithmetic at `p >= 2^32`, the same ratio being 124.6 at `p = 65537`.

Applied to this ladder, each external figure carries its own disclaimer in situ — III `n = 20` was
solved by Magma F4 in 259.27 s in 2015 **on a 1 TB machine**, and "that is a published fact about the
instance, not a comparison with the row above". What the external column establishes is better than a
time: **these instances are solvable by F4 on one machine**, so a future attempt has a target known
to exist.

**The startup floor, for comparisons that involve a separate process.** Where a comparand is another
program, a ratio within `FLOOR_MULTIPLE_REQUIRED = 2.0` of either operand's observed startup floor is
not an engine comparison and is marked, never dropped. The floor is derived from the board rather
than configured, needs `ROWS_FOR_A_FLOOR = 4` answered rows first, and its effect is the single most
useful thing the cross-library sweep produced: on the 28-pair cohort, **21 of 28 answered pairs were
disqualified — every one of them reading as a Zeebra win**, by factors up to 501x. Cite the cohort
when citing that figure: later boards read 89 of 116, and the current generated board 145 of 184.

**Note the asymmetry for #77's own comparison.** The floor rule lives on the cross-library
`Speedup`, not on the scoreboard's `Comparison`. Two Zeebra algorithms compared on one rung share a
process and have no startup charge, so the floor has nothing to bite on; the intra-Zeebra guard is
the weaker ±20% readability band. That is intended, and is stated here so a reader does not look for
a floor that is not there.

## 7. The baseline column

F4 + FGLM + `solve_one`, which is the only candidate that exists today — populating the column
validates the methodology before there is anything to compare. All rows: `machine=fedora`,
`cpu="8 logical, affinity 0-7"`, `concurrency=1`, `build="release, RUSTFLAGS=default"`, under the
standing policy of 200 000 columns and 20 000 000 live entries.

A witness row quotes its **fastest verified run**; a stopped row quotes the **observed range** over
every committed run, because the stop is deterministic and the wall is not (below). Counts are
`n` committed records.

| rung | vars | eqs | field | outcome | elapsed | n | est. bytes | measured `VmHWM` | witness |
| --- | ---: | ---: | --- | --- | ---: | ---: | ---: | ---: | --- |
| III `n=10` | 10 | 20 | GF(31) | **verified witness** | **106.4 ms** | 2 | 2 695 192 | — | **yes** |
| III `n=15` | 15 | 30 | GF(31) | **verified witness** | **7 798.5 ms** | 3 | 34 303 736 | — | **yes** |
| III `n=20` | 20 | 40 | GF(31) | stopped, `max_live_nonzeros`, degree 5 (4 completed) | 66 933–67 496 ms | 2 | 195 474 568 | 1 954 025 472 | no |
| VI `n=10` | 10 | 7 | GF(31) | **verified witness**, 6 of 8 slices | **577.8 ms** best witness slice | 9 | ~4.6 MB/slice | — | **yes** |
| VI `n=15` | 15 | 10 | GF(31) | campaign reached **no verdict**; each slice stopped at degree 9 (8 completed) | 29 498 ms per slice, 236 998 ms campaign | 9 | ~217.9 MB | — | no |
| VI `n=24` | 24 | 16 | GF(31) | stopped, `max_live_nonzeros`, degree 6 (5 completed) | 42 128–44 332 ms | 6 | 229 430 112 | 1 383 432 192 | no |
| V `n=24` | 24 | 16 | GF(2^8) | stopped, `max_live_nonzeros`, degree 6 (5 completed) | 105 070–111 063 ms | 4 | 236 351 760 | 1 393 819 648 | no |
| III `n=34` | 34 | 68 | GF(31) | **not attempted** — registered to show the gap | — | 0 | — | — | — |

One figure in that table is deliberately not the smallest number available. VI `n = 10`'s fastest
*run* is 569.1 ms and is an **empty slice** — `slice_established_nothing`, which established nothing
about the instance. The fastest run that produced a witness is 577.8 ms, and that is the one a
"time to a verified solution" column may carry. A table built by taking minima would have reported
the empty slice.

**Seven of eight rungs have a figure; three have a verified witness; four are documented resource
stops; one is deliberately unattempted.** Every stop is `max_live_nonzeros` against the
20 000 000-entry cap, with the degree reached and the last completed degree recorded.

Reproduce any row with `tools/fetch-mq-challenge.sh && tools/scoreboard.sh mq <id> [--seeds n]`,
which wraps `examples/scoreboard.rs`; each record carries its own command in its `reproduce` field.

Two readings the table supports and one it does not:

- **The stop is deterministic and the wall clock is not.** VI `n = 24` stops at 20 010 753 entries
  at degree 6 with a largest matrix of 13 602 x 19 132 on every run; its wall has read 42.1, 43.2,
  43.4, 44.3, 50.9 and 65.6 s. Everything except the wall row is a property of the instance.
- **The field costs about 2.5x at a fixed matrix.** V and VI at `n = 24` produce the *same* matrix
  shape and nearly the same entry count, and differ 111.1 s against 44.3 s at the slowest committed run of each, 105.1 against 42.1 at the fastest. That is a wall ratio at
  a fixed matrix, **not an attribution**: which part of the GF(2^8) multiply dominates is not
  measured.
- **It does not support a comparison with the external column.** §6.

Four rungs stop where they do **by authorization, not by capability**: §9 withholds authorization for
a III `n = 20` completion attempt and for any type VI `n = 15` campaign past the diagnostic. #77's
go/no-go — "if the baseline cannot be populated on any public instance, that is a finding that blocks
the epic" — passes on three rungs, and the authorization boundary is why the others are stops.

## 8. The reporting template

A B1/B2/B3 author reports, per rung:

1. **Primary**: wall clock to a verified solution, and peak bytes — stating which peak, and whether
   it is attributable to the row alone.
2. **Outcome**: one of verified witness / witness rejected / stopped at limit (with resource, detail,
   degree, last completed stage) / slice established nothing / not attempted.
3. **Secondaries**, labelled with the algorithm they belong to and never placed in a shared column
   with another algorithm's (§2).
4. **Figure basis** for every number: measured / fitted / predicted / extrapolated, with `Measured`
   naming its instrument and `Fitted` carrying its residual and applicability limit.
5. **Environment**: machine, cpu, concurrency, build, and the commit with a resolvable stamp.
6. **External reference points**, if any, each with hardware and software, and explicitly not as a
   ratio (§6).
7. **Negative results as deliverables**, not omissions.

The rendered form already exists and should be reused rather than reinvented: `SCOREBOARD.md`'s
headline and stop tables, generated, with the three classes never added together. Its three machine-
readable companions carry their contracts in-band — `history.json` is **append-only** and "array
position is the only record of when a run was taken"; `best.json` is "the fastest verified witness
per problem **among single-threaded runs**"; `solved.json` is "one verified witness per problem at
**any** concurrency — an existence claim, not a ranking".

## 9. What is missing

Honest list, so the next algorithm's author knows what this methodology does not yet give them.

1. **Per-rung expectations are retrospective** (§3.1). `Rung` exists and carries no Fukuoka rung; the
   challenge registry has no difficulty field. An expectation stated after the run cannot play #77's
   role.
2. **The primary metric's peak-bytes half is unpopulated where it matters** (§1.2). No rung has both
   a verified witness and an attributable measured peak.
3. **The metric is unexercised by a second algorithm.** One candidate exists. `Stage::Elimination`
   anticipates a non-Gröbner route and the Poseidon rows use a `resultant` formulation, so the type
   is ready; but no crossbred, XL or enumeration row exists on any Fukuoka rung, so "the primary
   metric is identical across algorithms" is asserted and not yet demonstrated. #76's own reading is
   that XL at the record size is 550x beyond Zeebra's largest matrix.
4. **Secondary non-comparability is a rule here, not a type** (§2).
5. **"Peak bytes" is not reconciled across the two boards.** The scoreboard has an estimate plus an
   optional `VmHWM`; the competitive board has four named bases; `FigureBasis::Measured` carries a
   free-text instrument. Nothing reconciles them, and this document picks the scoreboard's pair for
   #77's purposes without claiming that settles it.
