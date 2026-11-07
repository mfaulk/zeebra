# The external comparison protocol: what a cross-library measurement must record, and what it may claim

Policy for #257, binding on every figure in `research/competitive/` and on every adapter built to
the `#258` runner contract (`src/grobner/external/contract.rs`).

Zeebra's reason for comparing itself with msolve, Groebner.jl, Sagebrush and Singular is to find
out where its F4 actually stands. That is only worth doing if the answer can be trusted, and a
cross-library Gröbner benchmark has an unusually rich set of ways to be false while looking
careful. The two that matter most, and that organize this document:

1. **Quoting a ratio against a comparand that could not accept the input.** A tool with a 31-bit
   prime-field limit asked for Goldilocks has not lost a race. Reporting "Zeebra is 40x faster" in
   that situation is not an imprecise measurement, it is a false statement, and it is the single
   easiest mistake to make because the comparand *does* produce an error in some finite time.
2. **Comparing two different tasks.** A reduced grevlex basis, a lex basis, and one solution in the
   coefficient field are three different computations with three different costs. A tool that
   offers the cheap one has not beaten a tool that was asked for the expensive one.

Everything below exists to make those two unstateable rather than merely discouraged. Where the
rule is enforced in code rather than by convention, the enforcing function is named.

---

## 1. The task taxonomy, and the prohibition on conflating its members

A comparison is meaningful only between **equivalent tasks on the same mathematical input**. The
tasks are these, and they are `Task` in the runner contract, each with a stable tag that appears in
every record:

| Task | `tag()` | Output | Why it is its own row |
|---|---|---|---|
| Reduced Gröbner basis | `reduced-grobner-basis` | the unique reduced basis under the declared order | unique given the ideal and the order, so two libraries' answers compare as an *equality* |
| Lex basis | `lex-basis` | a Gröbner basis under lex, route unconstrained | the output is the same as above at lex; the row exists so a tool may choose its route |
| Lex basis by order conversion | `lex-basis-by-conversion` | a lex basis obtained from a degree-order basis, FGLM-style | different complexity from computing at lex directly; a tool offering only one route has not lost to a tool offering the other |
| One finite-field solution | `one-finite-field-solution` | one point in `F^n` satisfying the system | can stop at the first solution found, so strictly cheaper than enumerating |
| All finite-field solutions | `all-finite-field-solutions` | every point in `F^n` | |
| Univariate eliminant | `univariate-eliminant` | a generator of the elimination ideal in the last variable | obtainable without the rest of the basis by some routes |
| Cryptanalytic witness | `cryptanalytic-witness` | a CICO preimage or collision, checked against the primitive | the only task whose correctness check is not algebraic; **belongs to the cryptanalysis scoreboard, not here** |

**Rules.**

- A board column is one task. A figure for one task may never be placed in another's column, and a
  cheaper member may never be substituted for an expensive one and reported as the expensive one.
- `RunReport::speedup_over` refuses `NotComparable::DifferentTasks`. There is no other place in the
  codebase where a ratio is computed, so this is not avoidable by a caller.
- When a tool reaches an equivalent output by a different route, the route is recorded in the
  `stages` field and the task stays the same. When the *output* differs, the task differs.
- A task a tool does not offer is `Unsupported::Task`, not a slow run and not a failure.

### The conflation that is easiest to commit

Zeebra's own pipeline computes a grevlex basis, converts to lex, and then searches for a root, and
it times the three stages separately (`examples/scoreboard.rs` does this deliberately). msolve's
default mode produces a rational parametrization. Groebner.jl's `groebner` produces a basis. These
are **not** the same task, and a table that put msolve's end-to-end time against Zeebra's F4 stage
would be comparing a solve against a basis computation. Each library's invocation must be chosen so
that the output is the task's output, and the chosen flags recorded (§2, *operation requested*).

---

## 2. The fields every measurement must record, and how each is obtained

A figure without these is not publishable. The "method" column is the point: a field whose
measurement method is unstated is a field two runs can disagree on without either being wrong.

### Problem identity

| Field | Method |
|---|---|
| Problem id | The corpus name, e.g. `katsura-8`. For humans; **not** the identity. |
| Identity digest | SHA-256 over `Instance::canonical()` — field, extension degree and defining polynomial, monomial order, variable names in order, transformation, then every generator, one per line, ASCII. `Instance::digest()`. Two runs with different digests are different problems and `speedup_over` refuses them. |
| Family | `katsura`, `cyclic`, `mq`, `poseidon`, `anemoi`, … for grouping only. |
| Coefficient field | Characteristic **and** extension degree **and**, for an extension, the defining polynomial. `FieldSpec`. Characteristic alone is insufficient: `GF(2)` and `GF(2^8)` share one, and two libraries' default `GF(2^8)` need not be the same ring — different Conway polynomials give isomorphic but not identical representations, and bases compared element by element across them disagree for no mathematical reason. |
| Variable names, in order | Recorded as an ordered list and declared to the tool in that order. Not cosmetic: under lex, `[x1,x2]` and `[x2,x1]` are different orders with different bases. A tool that reorders them has answered a different question. |
| Monomial ordering | `lex` / `grlex` / `grevlex`, by `order_tag`. The tool's own name for it is recorded in the adapter and verified, not assumed — Singular's `dp` is grevlex and `Dp` is grlex, which is a one-character difference between two different answers. |
| Input equations | The exact generator text handed to the tool, byte for byte. Text is the interface, so this is recoverable from the run's input file. |
| Transformation | Any change to the mathematical problem before solving: field equations added, variables eliminated, a slice fixed, homogenization. **A transformed instance is a different ideal** and its digest differs. Absent means none. |

### What was asked

| Field | Method |
|---|---|
| Operation requested | A `Task` tag, plus the tool flags or script that implement it. The flags are part of the measurement: msolve `-g 2` and msolve default are not the same request. |
| Resource limits | `Limits`: wall-clock seconds, worker count, memory ceiling if any, and any tool-specific cap as the flag that set it. **Declared before the run, never discovered.** A run that stopped at 600 s means nothing without the 600, and two runs under different limits are not comparable even when both finished — `Limits::comparable_with` is the check and `speedup_over` applies it. |

### Which software

| Field | Method |
|---|---|
| Solver id | `singular`, `msolve`, `groebner.jl`, `sagebrush`, `zeebra`. `ExternalSolver::id()`. |
| Version | Obtained by **running the tool**, once per sweep, through `probe_version()` — never read from a package manifest, which can describe a build that is not the one on the path. Singular reports a build number (`4.4.1`, build `44105`); Groebner.jl a package version; msolve a version string. The raw text is kept beside the parsed value so a misparse is recoverable. |
| Build configuration | For Zeebra: the cargo profile and `RUSTFLAGS`, which is `Environment::build` in the existing scoreboard. For an external tool: how it was obtained (distribution package, source build) and the relevant flags. A source build at `-march=native` and a distribution build are different software. |
| CPU ISA floor | The instruction-set baseline the binary was compiled for. This repo has measured a 4-byte-vector loss from an unset `-C target-cpu` (`util::isa_floor`, and the figures corrected in #185/#231) — a comparison between a tool built for its distribution's baseline and one built for the host is not a comparison of algorithms. Record it; where it cannot be determined for an external binary, record that it could not. |

### Which hardware, and how much of it

| Field | Method |
|---|---|
| CPU model | `/proc/cpuinfo` model name, as `Environment::cpu` already records. |
| Affinity | The CPU set the run was pinned to. **Pinning is applied to the harness process**, not to each child: affinity is inherited across `fork` and preserved across `exec`, and wrapping each child in `taskset` is the first step toward the wrapper hazard in §4. `ZEEBRA_AFFINITY` records it. |
| Worker count | `Limits::workers`, and the flag that told the tool to use it. Part of the comparison key: a single-threaded tool has not lost to a tool given 64 cores. The cryptanalysis scoreboard already refuses cross-concurrency comparison (`ScoreboardError::DifferentConcurrency`) and this board inherits the rule. |
| Machine tag | `ZEEBRA_MACHINE`. Two figures from different machines are not a ratio. |
| Serialization | Every timed run holds the benchmark lock (`tools/benchlock.sh`), whose `QUEUED`/`START`/`END` log makes **overlapping windows a machine-checkable proof that two figures were not taken under the protocol**. A figure taken without the lock is not publishable. |

### What it cost

| Field | Method |
|---|---|
| Wall-clock time | Measured by `Supervisor` from just before `spawn` to the reap. Includes process startup, which is honest: starting Julia is part of what asking Groebner.jl costs. Excludes writing the input file and parsing the output, which are the harness's costs and not the solver's. |
| CPU time | `utime + stime` from `/proc/<pid>/stat`, converted at `USER_HZ = 100`. Polled, so it is the last reading before exit and can undercount the final poll interval; covers the child only. `CpuBasis::ProcStatTicks` records the conversion. Reported as `None` where `/proc` is unavailable, never as zero. |
| Peak RSS | §4. **Recorded with its basis** (`RssBasis`), because the two available methods are not the same kind of quantity. |
| Stage timings | Only what the tool itself reports, with the tool's own names, and the sum need not equal the wall time. A harness-derived "stage" is a fiction about another program's internals. |
| Entry-count estimate | Zeebra-only, and never placed in the same column as a measurement. `GrobnerFrontier::peak_estimated_bytes` is entries times 16 bytes; it differs from the process peak by a factor of ~75 on an F4 row. `RunRecord::measured_to_estimated_ratio` reports the factor, which is the interesting quantity. No external tool exposes the analogous accounting, so this column is empty for them — and empty, not zero. |

### What came out, and whether it was right

| Field | Method |
|---|---|
| Outcome | One of `RunStatus`'s five: `Complete`, `Verified`, `StoppedByLimit`, `Unsupported`, `Failed`. §3. |
| Invariants | The implementation-independent quantities extracted from the answer: quotient dimension, the sorted leading monomials of the reduced basis, basis cardinality, solution count, eliminant degree. `Invariants`. §5. |
| Verification | What independently agreed, and **how many invariants were actually shared** (`Verification::shared_invariants`). Zero shared invariants is not a verification, and `RunStatus::is_verified` returns false in that case — two empty invariant sets agree vacuously, which is the trap this guards. |
| Failure or limit | `LimitStop` names the resource and the limit; `RunFailure` names the mode (`Unavailable`, `Reported`, `Incomplete`, `MissingMarker`, `Unparsable`, `SelfInconsistent`, `NonZeroExit`, `Io`, `Environment`); `Unsupported` names the missing capability and the tool's own bound. §3. |
| Reproduction command | The exact command line, shell-quoted, including the environment variables set for the child. `Invocation::command_line()`. Plus the input file, which is recoverable from the identity digest's canonical text. |
| Raw log | Kept for every failure. A parse error is not diagnosable without it, and a failure with no log is an assertion rather than a finding. |

---

## 3. Encoding failure so that "cannot" is never read as "slower"

The five outcomes, and what each licenses:

| Outcome | Is there a time? | May it appear in a ratio? | How the board renders it |
|---|---|---|---|
| `Complete(Answer)` | yes | yes, marked unverified | the time |
| `Verified(Answer, Verification)` | yes | yes | the time |
| `StoppedByLimit(LimitStop)` | the time **is the limit** | **no** | `> 600 s (wall limit)` |
| `Unsupported(Unsupported)` | **no** | **no** | the missing capability, e.g. `field > 2^31` |
| `Failed(RunFailure)` | the time to fail, or none at all when the run was never attempted (`Unavailable`, `Environment`) | **no** | the failure mode |

`RunStatus::is_timing_evidence()` is this table's third column, and `speedup_over` consults it for
**both** operands. The prohibitions:

- **No speedup may be quoted when the comparand's status is not timing evidence.** Not as a lower
  bound, not as "at least", not with a footnote. If msolve cannot represent the field, the cell
  holds `field > 2^31` and there is no number in it.
- A limit stop is a **lower bound on the time the tool needs** and nothing else. It may be written
  `> 600 s`. It may not be used as 600 s in an arithmetic expression, and it may not be described as
  the tool "failing" — the limit was the harness's choice.
- An absent tool (`RunFailure::Unavailable`) is a **skipped row**, reported as skipped. `probe_version`
  is called once per sweep precisely so that this is discovered once rather than per instance.
- A run refused because of **the harness's own environment** (`RunFailure::Environment`) is a
  skipped row for the same reason: nothing ran. This is the case where something inherited would
  have selected a different algorithm, a different thread count, or polluted the output being
  parsed — and an adapter can set a child's environment but cannot *clear* it, so the condition
  cannot be fixed from inside the run. It is deliberately not `Reported`, which means "the tool
  printed an error": there was no tool execution to print one. The variant names the variable, so
  an operator is told what to unset, and the effect, so the refusal can be judged rather than
  merely obeyed. The live instance is Sagebrush's seven `SB_*` switches, every one read with
  `env::var(..).is_ok()` — truthy if set, so `SB_SIGF4=0` *enables* the experimental signature
  path — two of which also write a trace into the stream the basis is parsed from.
- `RunReport::was_skipped()` covers `Unsupported`, `Unavailable` and `Environment` together,
  because all three mean "not attempted" rather than "attempted and lost".
- A tool that contradicts itself (`SelfInconsistent`) produces **no finding at all**. Nothing may be
  concluded about any other implementation from a run in which the reference was unsound. This is
  not hypothetical: Singular's `std` under lex is cross-checked against its own `fglm` precisely
  because they can disagree.
- **A clean exit status is not evidence of success.** Singular exits 0 after a script error. Every
  adapter must establish its own positive evidence of completion — a terminal marker plus the
  absence of an error line — before any number it printed is trusted.

### Two measured capability gaps, which are results and not apologies

Both come from #308's provisioning survey, and both are findings the competitive report should
lead with rather than footnote. They are the concrete shape of the milestone's requirement not to
fabricate comparisons.

**The solution tasks have no external comparand at all.** `Task::OneFiniteFieldSolution` and
`Task::AllFiniteFieldSolutions` are **unsupported by all four comparands**: msolve returns a
rational parametrization rather than explicit finite-field points, and Groebner.jl, Sagebrush and
Singular ship no finite-field solver to drive. So those two columns are empty at *every* field
size, for every engine, and no amount of tuning changes it. This is the cleanest possible
illustration of why `Unsupported` has to be a separate outcome: were it folded into "failed" or
left as a missing row, the table would read as though Zeebra's solver had never been compared
because nobody got round to it, when in fact there is nothing to compare it against.

**The field ceiling, stated once.** msolve caps at **p ≤ 2^31 − 1** (`iofiles.c:563-564`, confirmed
by running it) and Singular is identical. Therefore:

| Zeebra field width | Engines that can accept it |
|---|---|
| ≤ 2^31 − 1 | msolve, Singular, Groebner.jl, Sagebrush |
| 32–64 bit (Goldilocks, KoalaBear-derived) | Groebner.jl and Sagebrush only — **and they cannot corroborate each other against a third** |
| 254/255-bit (BN254, BLS12-381 scalar fields) | **none, at any size** |

The second row is the uncomfortable one: a two-engine agreement is weaker evidence than it looks,
because the differential harness's whole argument for Singular as an oracle is that its `std` is
Buchberger/slimgb lineage and therefore *algorithmically* independent. Two engines that agree prove
less than two engines that agree for different reasons. Where only Groebner.jl and Sagebrush are
available, the row says so.

The third row means Zeebra's widest fields are validated by its own cross-field agreement and by
`ark-ff` on the arithmetic, not by any Gröbner comparand. That is a statement about the state of
the available tools, and the report makes it rather than quietly omitting those rows.

This is also why the corpus's reference characteristic is `2^31 − 1` and not something wider: see
`docs/research/cross-library-corpus.md`. A corpus on a 64-bit prime would render most of the table
`Unsupported` and measure nothing.

### Capability bounds are declared, not discovered

A tool's limits are stated as constants in its adapter and checked by `supports()` **before
anything runs** — `differential::MAX_CHARACTERISTIC = 1 << 31` is the pattern. This matters because
a bound discovered by running is a bound discovered as a `Failed` run, which looks like a defect;
declared, it is `Unsupported`, which is a fact about the tool. `supports()` is also re-checked
inside `run()`, so a harness that forgot to call it still cannot obtain a number.

`supports()` must answer only about **declared capability** — a field bound, an absent task, a
variable limit. It must never guess whether a run would finish. That is what `Limits` and
`StoppedByLimit` are for, and conflating them would reintroduce the error this document starts
with from the other direction.

---

## 4. Peak RSS: whose process, and exact or sampled

`crate::util::peak_resident_bytes` reads `VmHWM` from `/proc/self/status` — the *harness's* mark. An
external solver is a different address space and never appears there. The measurement must come
from the child, and the pid must be the solver's.

**The wrapper hazard.** `timeout 600 msolve …` makes `timeout` the direct child and `msolve` its
child; `timeout`'s own `VmHWM` is a couple of megabytes. A naive read of the direct child therefore
reports ~2 MB for a run that used gigabytes — this repo has a recorded instance of exactly that
shape, wrong by about 7000x. `taskset` execs and so keeps the pid, which makes it safe by accident
of its implementation; `taskset … timeout … msolve` is not safe, and `sh -c` may fork or exec
depending on the command.

**The resolution is structural.** `Supervisor` spawns the solver binary directly and implements the
time limit itself, so the direct child always *is* the solver. Affinity goes on the harness
(§2, *affinity*). Where a forking wrapper genuinely cannot be avoided, `RssPolicy::ProcessTree` is
the escape hatch and marks its own figures as sampled.

Every figure carries its basis:

| `RssBasis` | What it is | Comparable with |
|---|---|---|
| `DirectChildHighWater` | `VmHWM` of the direct child, polled while it ran. Kernel-maintained, so **exact** for a single-process solver. | another `DirectChildHighWater` |
| `ProcessTreeSampled { interval, samples }` | max over polls of summed `VmRSS` over the child and descendants. **Sampled** — misses spikes shorter than `interval` — and an **over-count**, since shared pages are counted per process. | nothing, without saying so |
| `AllocatorTracked` | peak bytes **allocated**, from a tracking `#[global_allocator]` inside the measured process. Zeebra's own rows only. | another `AllocatorTracked` |
| `Unavailable` | not Linux, `/proc` unreadable, or the child exited before the first poll | nothing |

A figure on one basis may not be compared with a figure on another. This is the same discipline as
§2's estimate-versus-measurement rule, applied one level down.

### Two measured cases that show why the basis has to travel with the figure

Both are from this repo, and they fail in opposite directions.

**Allocated is not resident, and the gap can exceed the resident peak.** On the Fukuoka III
`n = 20` row (#237), a tracking allocator observed **21 674 MB** where `VmHWM` observed
**13 996 MB**. The cause is not slack spread across many allocations: F4's pair queue is a
`VecDeque` that doubles to `2^28` slots, which is a **single** reservation of 20 480 MiB, of which
roughly 60% is never written and therefore never becomes resident. One allocation larger than the
entire resident peak is why no amount of care in *reading* a number called "peak memory"
distinguishes the two quantities — only recording which one it is does. `RssBasis::AllocatorTracked`
exists so this cannot share a column with `VmHWM` by accident, and `examples/f4_memory.rs` reports
the two separately.

**A suspiciously exact number is also evidence.** A capped-versus-uncapped comparison of the same
row returned `14 336 724 kB` — **identical to the kilobyte** — across a 50x difference in the cap
and a 3x difference in runtime. The exactness is the finding: a sum of scattered allocations does
not reproduce to the kilobyte across two runs that did different amounts of work, so the figure is
dominated by one large reservation whose size the cap does not influence. That **withdraws**
`docs/research/f4-resource-scaling.md` §6a's 4 978 MB uncapped figure as a measurement error, and
with it the hypothesis that the refusal path was responsible.

The pair is worth keeping together. In the first case a *dirty* number — two figures that disagreed
by 55% — was the signal. In the second a *clean* one was. Neither would have been readable without
knowing which quantity had been measured.

### Attribution within the harness's own rows

For Zeebra's own rows the analogous question is which row a process peak belongs to. `VmHWM` is
process-wide, so a process that ran seven rows reports one figure covering all seven. Records
therefore carry `measured_peak_rows_in_process`: `Some(1)` means the figure is that row's, anything
larger means it is a ceiling over that many. `RunRecord::measured_peak_is_attributable()` is the
check, and `tools/scoreboard.sh`'s ladder tier runs one process per row so that the answer is one.
An absent count is **not** attributable — records written before the field existed cannot have the
number recovered.

---

## 5. Invariants must agree before any timing is published

Two libraries' bases may be printed in a different order, with a different sign convention, and with
a different generator order, while being the same ideal's reduced basis. A textual diff is therefore
the wrong test. What is genuinely implementation-independent:

- **Quotient dimension** `dim_k k[x]/I` — the number of standard monomials. Finite exactly when the
  ideal is zero-dimensional.
- **Leading monomials of the reduced basis**, sorted — the initial ideal, an invariant of the ideal
  and the order. Two correct reduced bases under the same order have the same one.
- **Basis cardinality** — implied by the above, and useful alone when a tool reports only a count.
- **Solution count** in the coefficient field.
- **Eliminant degree**.

`Invariants::agree()` returns the disagreements, and it compares **only the fields both sides
carry**. An absent field is "not reported", never zero and never evidence of agreement — so
`Invariants::overlap()` must be consulted too: an empty disagreement list over an empty overlap is
not a verification, and `RunStatus::is_verified` enforces that distinction.

**The gate.** No timing for a problem is published until the invariants of every library's answer on
that problem agree. A disagreement is not a weaker result; it means at least one library is wrong, or
the two were given different ideals, and either way the timings compare nothing. `Verification::of`
returns `Err` on a disagreement rather than a lower-confidence `Ok`.

Corollary for the corpus: **publish no timing for a family whose ideal equivalence has not been
verified.** See `docs/research/cross-library-corpus.md`, where the per-family status is recorded.

---

## 6. Where the rows live: a separate board, and why the data model says so

**Decision: a new board at `research/competitive/`, carrying `library` as a first-class dimension.
The cryptanalysis scoreboard at `research/scoreboard/` is not extended.**

The milestone instructs that the cryptanalysis scoreboard must not be overloaded with different
semantics. That instruction is not the argument; it happens to coincide with what the existing data
model already says. Six reasons, each from the code:

1. **Identity is validated against a cryptanalysis registry.** `Scoreboard::add` refuses any run
   whose `challenge` is not in `research::registry()` and whose digest does not match the current
   `ChallengeManifest` (`ScoreboardError::UnknownChallenge`, `StaleIdentity`). That check is the
   scoreboard's main value, and it is a check against a registry of *published cryptanalytic
   problems*. Katsura, Cyclic and random MQ are not that. Registering them would mean giving each a
   `Significance`, a `CicoTarget`, a `DisclosedMethod` and an `ExternalStatus` — fields about
   published bounties and claimed attacks — with nothing to put in them.

2. **The outcome vocabulary is about witnesses, not answers.** `RunOutcome::is_verified_witness`
   means a preimage was found and checked against the primitive. There is no such thing for a
   Gröbner basis. The competitive board needs the contract's five-way `RunStatus`, which
   distinguishes *unsupported* — a distinction `RunOutcome` has no variant for and could not
   acquire without changing what every existing record means.

3. **Adding a `library` column would make the existing summaries wrong.** `Scoreboard::best` is
   "the fastest verified witness per problem among single-threaded runs", keyed on `challenge`.
   With a library dimension it would silently return the fastest *library* for each problem and
   present it as the problem's row, and `verified_somehow`'s one-entry-per-problem contract would
   become one-entry-per-problem-across-libraries. Both files are machine-readable contracts that
   consumers already depend on; this is precisely the overloading to avoid.

4. **`Comparison::of` cannot express the central distinction.** It refuses `DifferentProblems` and
   `DifferentConcurrency`, which is right, but it has no notion of an unsupported input. A library
   that could not represent the instance would have to be encoded as a *missing record*, which
   renders as a gap — indistinguishable from a row nobody ran, and the opposite of the explicit
   capability statement §3 requires.

5. **`GrobnerFrontier` is Zeebra's F4 internals.** Batch counts, degree profiles, Macaulay matrix
   entries, `peak_estimated_bytes` at 16 bytes an entry. No external library exposes any of it. A
   shared record would carry a mostly-empty structure whose one populated field means something
   different per row, which is how an estimate gets compared with a measurement.

6. **The history has a different meaning.** `results/history.json` is append-only and
   `results/solved.json` answers "which of these ciphers has a verified break". Mixing library rows
   in would change the answer to that question without changing the question.

What the new board **does** reuse, because these are the conventions that make the existing one
trustworthy: hand-rolled JSON through `research::record::Json` (no serde in this subsystem), a
generated Markdown renderer so the human-readable table cannot drift from the data, identity frozen
by digest, unsuccessful runs recorded rather than dropped, and an append-only history with its
contract written into the file.

---

## 7. Ratios

A speedup may be computed only when **all** of these hold, and `RunReport::speedup_over` checks
each:

1. the same instance digest,
2. the same `Task`,
3. identical `Limits` — wall, workers, memory ceiling, tool caps,
4. both statuses are timing evidence,
5. a non-zero denominator,

and, not expressible in the type and therefore required of the operator:

6. the same machine, the same affinity, and both runs under the benchmark lock with
   non-overlapping `START..END` windows,
7. the invariants of both answers agreed (§5).

For every other pair the cell records **the resource limit or the missing capability instead of a
ratio**. There is no "approximately" in this section.

---

## 8. Licensing

Running a GPL binary as a separate process places no obligation on Zeebra's MIT core, and that is
the only thing any adapter does: it writes an input file, spawns a process, and parses text. msolve,
Groebner.jl and Singular are GPL and are **algorithmic reference only** — no source may be copied
into Zeebra. Sagebrush is MIT OR Apache-2.0 and reuse is permitted. Fukuoka MQ Challenge instances
are "All Rights Reserved, no stated licence" and **must never be redistributed**; they are fetched
locally by `tools/fetch-mq-challenge.sh` into `ZEEBRA_MQ_DIR` and referenced by digest. See
`docs/research/external-provenance-policy.md`, which is the authority.

---

## 9. Reproducing a published figure

Every row carries what is needed, and nothing else is required:

1. The identity digest's canonical text reconstructs the exact input.
2. The reproduction command line, including the environment set for the child.
3. The version string the tool reported, and the build configuration.
4. The machine tag, CPU model and affinity.
5. The limits.

If a row cannot be reproduced from those five, the row is the defect, not the reproduction attempt.
