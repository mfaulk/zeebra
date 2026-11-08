# The external comparison protocol: what a cross-library measurement must record, and what it may claim

**Measured at:** publication bound `2e722797` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](#10-the-commit-and-what-a-publication-bound-is)).

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
| Source commit | For Zeebra: the SHA the measured binary was built from, `Environment::commit`, read with `git rev-parse` at run time — never a branch name, which stops identifying a binary as soon as the branch moves, and never a date, which at this repository's commit rate names no commit at all. For a comparand: the version or pin `external-comparands.md` records. A figure without it cannot be re-taken, which is #335; what a commit does and does not buy is §10. |
| Build configuration | For Zeebra: the cargo profile and `RUSTFLAGS`, which is `Environment::build` in the existing scoreboard. For an external tool: how it was obtained (distribution package, source build) and the relevant flags. A source build at `-march=native` and a distribution build are different software. |
| CPU ISA floor | The instruction-set baseline the binary was compiled for. This repo has measured a 4-byte-vector loss from an unset `-C target-cpu` (`util::isa_floor`, and the figures corrected in #185/#231) — a comparison between a tool built for its distribution's baseline and one built for the host is not a comparison of algorithms. Record it; where it cannot be determined for an external binary, record that it could not. **For a comparand this repository builds from source, match it rather than record it** — see below. |

#### A comparand built here is built like Zeebra's side

"Record the floor" is the rule for a binary somebody else shipped. It is the wrong rule for a
comparand whose build *this* repository owns, and the Sagebrush driver was the live instance (#385):
`tools/external/provision.sh` builds it outside Zeebra's worktree, so it inherited neither
`.cargo/config.toml` nor the workspace `[profile.release]`, and the comparand was compiled at
baseline `x86-64` with no LTO while Zeebra's own side ran at `x86-64-v3` under fat LTO at one
codegen unit.

Resolved by **matching the floor**, not by recording the gap. Three parts, and the last two are
what make it checkable rather than asserted:

1. The rustflag is passed at the build site and the profile is restated in the driver's own
   `Cargo.toml`, because profiles live in `Cargo.toml` and a copied `.cargo/config.toml` carries no
   `[profile]` section. The recipe is the README's "An out-of-tree measurement harness".
2. **The comparand reports its own floor.** `sagebrush-gb-driver` prints `#isa floor:` from a
   compile-time `cfg!(target_feature = ..)` inside the binary that ran, and the adapter carries it
   into the row's `ToolVersion`. The script states what it *asks for*; only the binary can state
   what it *is*.
3. **The marker is required.** It arrived with driver contract 3, so a binary installed before the
   change is refused rather than measured — otherwise a stale baseline build would silently produce
   rows that read as `x86-64-v3` because the script now says so.

A static probe of the built artifact is **not** an acceptable substitute, and #385 records the
measurements that killed one: rustc emits no GNU property note; "contains AVX2 or BMI2" is a false
positive because explicitly dispatched `#[target_feature]` kernels put those instructions in a
baseline build; and VEX share is a false negative in general because Rust's `std` is distributed
prebuilt at baseline. An instrument that can say "definitely absent" but not "definitely present"
gets read as the latter.

Two consequences worth stating plainly. Raising a comparand's floor makes the **comparand** faster,
so it is never a self-serving change. And it invalidates nothing that was recorded — the rows taken
before it say what they were taken against — but it does mean those rows are not comparable to the
current column at this standard, which is why re-taking them is its own serialized measurement
(#520).

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
- **A fact about the ideal is `Unsupported`, even when the tool announced it by exiting non-zero.**
  A task needing a finite quotient algebra does not apply to a positive-dimensional ideal; no tool
  can do it, so no tool failed. Four adapters derived that classification independently and two of
  them put it in the failure bucket — Singular's on `cyclic-4`, fixed in M26, and Sagebrush's on the
  same instance, fixed in M27 — so it is now the named variant `Unsupported::PositiveDimensional`,
  carrying the task that does not apply. A fifth adapter gets it by returning the variant rather
  than by rediscovering the rule; a driver's own error line is still the evidence the condition
  holds, but it is classified before the exit status is consulted.
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

### The eliminant is not one of those gaps, and was wrongly refused as though it were

`Task::UnivariateEliminant` was refused by **Zeebra's own adapter** in the same match arm as the two
solution tasks and the witness, under one comment saying "no comparand offers the task at all". That
reason holds for three of the four and is **false for the eliminant**: msolve serves it below
`MAX_CHARACTERISTIC_ELIMINANT = 1515531529`, and Singular has a dedicated arm computing a lex `std`
and reporting the last generator. So the eliminant was the only task this document defines with
**two external engines and no in-crate operand** — a corroboration gain that could not become a
competitive row, because the engine the board exists to measure would not answer (#465).

It is served now, and the reason it can be is that it is a **projection of an answer already
computed**: `I ∩ k[x_n]` is generated by the one element of a reduced lex basis involving no other
variable, so the adapter takes it off the lex basis it already produced. No new algorithm, and in
particular no root-finding strategy choice — which is what the original comment was objecting to,
and it objects only to the solution tasks.

Two things follow for reading an eliminant row:

- **The route differs per engine, and that is the measurement.** Zeebra goes grevlex F4 then FGLM,
  Singular a lex `std`, msolve its rational parametrization. Per the rules above, a different route
  to an equivalent output keeps the task and is recorded in `stages`.
- **The eliminant's degree and the quotient dimension coincide only for a radical ideal in shape
  position.** That is a precondition, not an identity, so both are reported as invariants and
  neither is derived from the other. Where they agree across engines the agreement is evidence;
  where they differ, the ideal is telling you something about itself.

**The field an eliminant comparison can live at is not the reference prime.** msolve's bound on
this task is `1515531529`, so at `corpus::REFERENCE_CHARACTERISTIC = 2^31 − 1` it is `Unsupported`
by design and the only comparand is Singular. The corpus's `ALTERNATE_CHARACTERISTIC = 2^30 + 3`
exists for exactly this, and `ZeebraSolver` compiles the ladder's dimensions there as well as at
the reference prime — un-refusing the task without that arm would have left the eliminant with two
external engines and still no Zeebra operand, which is #465's defect from the other direction.
`test_a_real_msolve_and_zeebra_return_the_same_eliminant` is the resulting check, and it compares
the **polynomial** rather than the rendering: both printers were made to agree, so a text
comparison would pass on a coincidence of formatting and fail on a harmless one.

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

### The board must state its own roster and its own exclusions

Two things about a run are invisible in a table of its rows, and both change what the table means.

**Which libraries were there.** A board taken on a machine where three of four engines were
unreachable renders exactly like a board taken where three were never asked for. The adapters all
return `Result<Self, RunFailure>` from their probe, and `RunFailure::Unavailable`'s own contract is
that "a sweep must continue, **the board must show the row as not attempted**" — so an unreachable
engine is recorded as a row, and `to_markdown` opens with a roster naming every library, its row
count, and how many of those rows are timing evidence. A library at zero answers is the signal that
a run lost an engine; without it, a lost engine and an unasked engine are the same artifact.

**How many ratios the gates removed.** §7's conditions are enforced in code and every excluded row
is marked individually, but a marked row is only visible to a reader who tallies the column. The
speedup section therefore states its counts first: total pairs, how many the startup floor
disqualified, how many carry no checked invariant, and of the publishable remainder how many sit
inside the 20% band results are read against. On the populated board that tally **is** the headline
— the survivors are a small minority of the pairs, and a reader who sees only them sees a different
comparison from the one that was run.

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

### 7.1 The wall-clock ratio, and the floor that disqualifies most of them

The ratio above is over **wall time**, which is the cost of *asking* and is the figure a caller
pays. It carries one further condition, enforced by `Speedup::is_engine_comparison`: neither
operand may be within 2x of its own library's observed startup floor. Singular's wall is ~36 ms on
everything up to `katsura-6` — its `exec` — so a `0.01x` there measures process creation and
nothing else, and four apparent Zeebra wins of 2.2x, 3.4x, 8.4x and **450x** were entirely that
floor.

The consequence is that the board publishes **no wall-clock engine comparison on either classical
family**, which is correct and is also a gap: the data for one is already recorded.

### 7.2 The engine-internal ratio: a second statistic, never a substitute

Every adapter records its tool's **self-reported stage times**, and those are inside the process.
The engine-internal ratio is taken over them, and it is a **separately named statistic with its own
column and its own refusals** (`EngineRatio`, #428). The floor guard is not relaxed, reinterpreted
or bypassed; this figure simply has no process startup in either operand, so that guard has nothing
to do.

**What it is.** The same pairing conditions 1–7 above, with each operand replaced by the sum of the
stages that constitute that library's own engine time for the task:

| library | reduced basis | lex basis by conversion | excluded, and why |
|---|---|---|---|
| `zeebra` | `basis` | `basis` + `conversion` | the `conversion:` sub-stages, which are inside `conversion`; and `quotient-dimension (for the invariant)`, which is work done to *report* an invariant |
| `singular` | `solve` | `source-basis` + `solve` | — |
| `groebner.jl` | `solve` | n/a — no FGLM | `process-wall` and `process-cpu`: Julia's compiler is exactly what this statistic excludes |
| `sagebrush` | `solve` | `solve` | — |
| `msolve` | `f4: overall(elapsed)` | `f4:` + `sparse-fglm: overall(elapsed)` | its named sub-stages, which would double-count its own total |

msolve's labels are its **own**, not translated: the correspondence with Zeebra's stage names is a
finding that belongs in its implementation study, and renaming it here would hide it.

**What it must say about itself.** It is **not an end-to-end cost** and may not be quoted as one.
The board prints that sentence above the table, in the same section as the figures, because a
reader who meets a `2.58x` without it will compare it against a wall-clock number somewhere else.

**When it refuses.** Three conditions, all of them visible in the cell rather than dropping the row:

1. **No usable stage.** A library that reports no stage this statistic can use contributes no row.
   Absent evidence is a refusal here, unlike the startup floor, where an unobservable floor is
   treated as acceptable — the asymmetry is deliberate: an unknown floor would silently drop rows,
   and a missing stage is visible as an em dash in the measurement table.
2. **A figure at its own granularity.** A tool-reported stage is only as good as the resolution it
   was printed at. Singular prints **whole milliseconds** and msolve `%.2f` seconds, so a `0.0 ms`
   stage is a printf and not a measurement. A figure must be at least **5x** its library's
   granularity, which bounds each operand's quantization error at ±10%; `katsura-4`'s `0.0 ms` is
   refused, `cyclic-6`'s 7 ms passes at ±7%. A zero-length engine time contributes no row at all,
   having no reciprocal.
3. **The provenance and invariant gates of §5 and §8**, unchanged: a problem with no recorded ideal
   equivalence, or a ratio between two unchecked answers, is refused exactly as in the wall-clock
   table.

**Every published figure carries its uncertainty.** The coarser operand's quantization is printed
beside the ratio — `2.58x ±5%` — because the gate admits figures at five granularity units and the
reader has to see which end of that they are looking at. Below half a percent it prints `±<1%`
rather than `±0%`, which quantization never supports.

**What it exposed.** On the two hardest classical rungs the board reaches, Zeebra's engine is
**2.58x ±5%** slower than Singular's on `katsura-7` and **1.88x ±7%** on `cyclic-6` — a gap the
board previously held and refused to report, because the wall-clock ratio on those rows is
`exec`. Against Groebner.jl's engine the same rung is **15.89x**, and against Sagebrush's
**8.67x**. The end-to-end column remains uncomparable at these sizes, and the fix for *that* is
bigger rungs rather than a different statistic.

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

6. The commit the measured binary was built from (§10).

If a row cannot be reproduced from those six, the row is the defect, not the reproduction attempt.

---

## 10. The commit, and what a publication bound is

A figure states the commit it was taken at. `Environment::commit` has held the field since the
scoreboard existed and `examples/scoreboard.rs` fills it from `git rev-parse`, so this was never a
missing capability — the gap was in the prose documents, which recorded the machine, the pinning,
the build flags and the lock, and never the commit (#335). What that cost is exact: #318 found a
figure on record 1.2x faster than the same measurement taken months later, and the one experiment
that settles such a thing — re-measure at the old commit — could not be *set up* from what was
written down. It took a separate archaeology pass to recover the SHA before the question could even
be asked.

### 10.1 The declaration

Every document under `docs/` that publishes a measurement carries one of three declarations in its
header:

| Declaration | Means |
|---|---|
| **Measured at:** `` `93bb1c2` `` | the commit, or the commits, the figures were taken at. The strong form, and the only one a new measurement may use. |
| **Measured at:** publication bound `` `x` ``…`` `y` `` | retrospective only: the figures were taken *at or before* the commits that published them, recovered from git rather than recorded at the time. §10.2. |
| **Measured at:** not measured here — … | the document takes no measurement; every figure is quoted from a cited source, which carries its own era. |
| **Measured at:** unrecorded — … | the era is genuinely unrecoverable, said out loud rather than left for the reader to assume. |

`Frozen at:` is the same declaration under another name, which `m27-baseline.md` already uses. A
section stating its own commit overrides the document's header for that section, and is what
`resultant-elimination.md` §6.13 does when it names both ends of an A/B by SHA rather than by
branch — `origin/main today` stops identifying a binary the moment `main` moves.

`tools/check-measurement-provenance.sh` enforces the declaration's presence, over
`docs/research/*.md` and `docs/MILESTONE-*.md`, and runs in CI. It was written because the
reproducibility checklist had asked for the commit for a milestone already and that did not produce
it.

### 10.2 A publication bound is weaker than a measurement's commit, and is labelled so

A figure already in a document whose commit nobody wrote down can still be dated, because the
commit that *wrote the figure into the document* is in git:

```sh
git log -S "37 634.3" --format='%h %ad' --date=short -- docs/research/resultant-elimination.md | tail -1
```

That returns `93bb1c25`, which is independently the commit `resultant-elimination.md` §6.5's table
was taken at. The recovery is cheap and it is an **upper bound**: the run happened at or before the
commit that published it, on a tree that was that branch's head and need not be the published
commit's tree. Dates do not substitute — this repository has run at ~200 commits a day, so a date
names no commit at all.

A bound is therefore never written into `Environment::commit`, whose contract is the commit the
measurement was taken at. A transcribed row with no commit on record keeps the empty string, which
the register renders as recorded-absent; the bound lives in the source document's header, which is
where the register's `source` column already points. Filling a measured-provenance field with an
inferred value is the same category error as reporting an estimate in a measured column.

### 10.3 The commit is necessary and is not sufficient

#318's resolution is the caution against reading a SHA as reproducibility. §6.5's figure does not
reproduce *at its own commit*: re-run at `93bb1c2` under the lock on one pinned core it gives
45 159.7–47 944.4 ms against the 37 634.3 ms on record, so no commit in the 435-commit range could
be responsible and the bisection the issue proposed would have landed nowhere. What differed was the
session and the ambient load — the width penalty is 6% and contention up to 1.4x, with three other
agents' `cargo test --release` runs resident during the original sweep, which `tools/benchlock.sh`
serializes benchmarks against but not builds.

So the era of a figure is the commit **and** the session **and** the load. `tools/benchlock.sh`
records `load=` on its START and END lines for the second half of that. A figure quoted across two
sessions is not comparable with itself, which is what `Attribution::IncomparableFigures` exists to
say.

And a commit that is recorded is not necessarily a commit that can be checked out: three of the four
competitive cohorts record branch commits that did not survive their pull request's squash merge, so
"re-measure at `7adb29e`" is an instruction nobody can carry out. That is #505, and it is a defect
in where the SHA is taken rather than in recording one.
