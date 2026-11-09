# M26 — Algorithmic Elimination and Competitive Solver Performance

**Measured at:** publication bound `91d32ece` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](research/external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

**Status:** planned.
**Prerequisite:** M25, complete and merged — `MILESTONE-COMPETITIVE-ALGEBRA.md`, including its §13
report.
**Board:** [Zeebra, project #7](https://github.com/users/mfaulk/projects/7), label `M26`.

M24 changed what counts as progress on a problem: a reproduction of something published, or a witness
for a registered instance nothing public has a witness for. M25 added the axis neither it nor M23
had — **an external comparand on this machine** — and the first thing that axis produced was two
measured deficits rather than a lead.

M26 is the milestone that spends them. Its unit of progress is **an asymptotic change or a closed
competitive gap, chosen by a measurement rather than by plausibility.**

### Revision history

| date | change |
|---|---|
| 2026-11-07 | Written from M25 §13.8/§13.9 and the post-report issues #349–#351. |

---

## 1. Prior evidence, and the three rules it imposes

M25's §13 report is the entire input to this plan. Three of its findings are load-bearing, and each
one forbids something M26 might otherwise do.

**Rule 1 — memory is measured before a run is authorized, not estimated after it.** M24 §10.1's
result, which M25 ran under and then confirmed again: every prediction about a stage already measured
held, and every prediction about a quantity nobody had measured was wrong, three of four by more than
an order of magnitude. The six-round symbolic build was predicted at ~68 MB and measured at **57.0
GB** — 838x.

**Rule 2 — a stage share is not a speedup, and the Amdahl screen settles kernel work.** Every
stage-level candidate M25 screened has a ceiling of **1.01x–2.59x**, at or near this machine's 20%
noise band. F4 elimination is **7–22%**, not M16's obsolete 65–88%. No kernel specialization can
produce a readable end-to-end result, and M26 does not schedule any.

**Rule 3 — a figure taken today is not comparable to a figure on record.** Determinant measurements
now run **~1.2x slower** than the same measurements on record — same registered row, same code path,
same lock, months apart (#318) — and the width penalty measures **31–44%** at 32 workers where §6.6
recorded **4–9%** (#319). Both were recorded as findings rather than repaired. **A ratio computed
across that boundary carries a ~20% systematic that is a property of neither implementation.**

### 1.1 The two measured deficits

| deficit | magnitude | instance | subsystem |
|---|---:|---|---|
| order conversion against msolve | **~30x** | Anemoi, one prime, same machine | FGLM |
| the basis stage against Singular | **4.11x** | `mq-random-10`, 29 963 ms against 7 291 ms | F4 |

They are in **different subsystems, on different families, against different engines**, and M25
deliberately funded neither blind. The conversion deficit is the larger, and conversion was **75% of
the Anemoi solve**; the basis deficit is on the corpus family closest in shape to a cryptanalytic
system, which is the family that matters most for the long-term objective.

M25 also recorded that the conversion deficit **narrows with the rung** — 21.1x at Anemoi `N = 5` to
**12.5x at `N = 6`** — which is a fact any conversion claim has to survive.

### 1.2 What M25 delivered that M26 builds on

| result | figure | issue |
|---|---|---|
| six-round symbolic build | **7.5x faster**, peak **175–179x** lower | #243 |
| F4 peak memory | **9.06x** lower, and 10% faster | #305 |
| Anemoi `N = 6` PCICO | solved over GF(65537), witness verified through the permutation | #286 |
| Euclidean remainder sequence, prototyped | **1 692x** at order 1 458 | #297 axis 4 |

The F4 memory reduction **did not change the solving limit**, and M26 does not report a memory saving
as a frontier extension.

### 1.3 One claim in circulation that this plan corrects

The recommendation this plan was drafted from asserted that #350's whole-run estimate "still charges
approximately 48 minutes for symbolic construction." **It does not.** Both §8.4.2 of the M25 document
and #350's own body use the corrected **5.4 min** figure, measured on the lock and cross-checked at
5.6 min. There is no stale cost model to repair, and no issue is filed for one.

The same recommendation described the 1 692x as something that "could make harder Poseidon instances
affordable." That is **overdrawn in the direction this repository has twice been burned by.** 1 692x
is the **stage**; the row receives **~3x**, because after axis 4 the six-round route is **78% root
finding**. #350 states in its own body that it does not raise the reachable round count, and it is
right.

---

## 2. Objectives

1. **Land an asymptotic improvement to bivariate elimination** — dense Sylvester determinants replaced
   by a polynomial remainder sequence, `O(n³)` to `O(n²)` in the degree — and take the
   `rf4-rp2` row from costed-and-refused to authorized-and-run or refused on a measured term.
2. **Decide the F4 investment from one profile instead of from a hypothesis**, and act on whichever
   answer it returns.
3. **Make order conversion competitive**, justified as parity and general capability rather than as
   frontier extension.
4. **Reduce retained basis memory** on the mechanism M25 measured, independent of either decision.
5. **Make the competitive board say what the adapters can already measure** — three working adapters
   currently produce zero retained records.

---

## 3. Scope, and explicit non-goals

**In scope:** the Euclidean remainder sequence in `src/`; root-finding cost at the degree the
six-round rows reach; one profile of `mq-random-10`'s stage split; a bounded certified Krylov
conversion prototype; duplicated basis storage during interreduction; the F4 entry-budget coupling;
scoreboard population; merge-result CI.

**Not in scope, each for a recorded reason:**

| excluded | reason |
|---|---|
| GPU and out-of-core (#69, #86–#89, #225) | Nothing in M25 produced the named kernel, workload, predicted benefit and benchmark that §3 requires before that work is scheduled — and #305 removed 9.06x from the memory pressure that was the main argument for it |
| F4 elimination kernel specialization (#269) | Rule 2. Amdahl ceiling 1.07x–1.29x, at or inside the noise band |
| Griffin/FreeLunch (#202, #306) | Costed and pinned in M25, but it buys **one family**. Deferred, not rejected; see §11 |
| Boolean/SAT comparison (#218–#221) | The first same-machine external baseline outside Gröbner, and genuinely attractive, but it needs characteristic-two formulation work and a fair SAT comparison first |
| MinRank | No smallest credible target is defined and the formulation cost is unestimated |
| An F4 matrix microbenchmark corpus (#262) | Rule 2 makes it valuable only if #349 implicates elimination. Gated on #349, not scheduled |
| `rf6-rp0`, any eight-round row | 16.15 h and ≥490.5 d respectively. Not near any ceiling, and not reachable by a constant factor |
| Increasing the round count | #350 does not do this and M26 does not claim it |

---

## 4. Issue reconciliation

### 4.1 Carried into M26 as written

| issue | workstream | why it carries |
|---|---|---|
| #349 | M26-0 | The profile that decides between #268 and a Krylov route. One run |
| #348 | M26-0 | The FGLM quotient-dimension cap cites a corpus figure the corpus outgrew by 105x |
| #318 | M26-0 | Rule 3's first half — the ~1.2x drift bounds every ratio M26 quotes |
| #319 | M26-0 | Rule 3's second half — 31–44% against a recorded 4–9% |
| #350 | M26-A | #297's axis 4. The asymptotic change this milestone is named for |
| #351 | M26-A | After axis 4 the route is 78% root finding, so this becomes the gating term |
| #297 | M26-A | The parent research issue. Axis 4 is recommended; axis 5 is ruled out at `R > 8.7` |
| #58 | M26-B | The FGLM half reopens. Its deferral was conditional on a named trigger and a measured gap against a maintained implementation is that trigger |
| #224 | M26-B | The alternatives survey, written before the gap was measured |
| #323 | M26-B | The attribution that forces the parity framing. See §5.3 |
| #304 | M26-C | The basis is held three times over during final interreduction — measured, not speculative |
| #322 | M26-C | F4's effective entry limit is `min(max_live_nonzeros, max_live_bytes / 16)`, so lifting one knob does nothing. This is what refused Anemoi `N = 6` |
| #268 | M26-C | **Conditional on #349.** Promoted only if the profile implicates its two stages |
| #330 | M26-C | **Conditional on #349.** Column indexing from symbolic preprocessing |
| #256 | M26-I | The competitive research parent |
| #339 | M26-I | A PR is tested against its base, not the merged result, so two green PRs can merge red. M25 hit this for real |
| #395 | M26-I | `max_wall_time` is checked once per batch and **never during final interreduction**, which #349 measured at 80.4% of `mq-random-10`, so a bounded run can overrun by an order of magnitude. A **prerequisite of #369**, which sets wall limits on rows that may not finish — an unhonored limit there records an incomplete row as a completed comparison |

Nineteen of the twenty issues above are attached as sub-issues of the M26 epic. **#297 is not**, and
the reason is mechanical rather than a scope judgement: GitHub permits an issue only one parent, #297
is already a sub-issue of #292, and M25's record is left intact rather than rewritten. #297's M26
scope is carried by the `M26` label and by §5.2 of this document, and a comment on the issue says so.

### 4.2 New issues

| issue | workstream | why it did not exist |
|---|---|---|
| #367 | M26-A | §8.4.2 left `rf4-rp2` as a decision pending two measurements; nothing tracked taking the decision |
| #368 | M26-B | #58 is a decision and #224 is a survey. The staged implementation had no issue |
| #369 | M26-I | The adapters closed in M25; populating the board with them did not |
| #370 | M26-I | The integration-and-report role, mirroring #299 |

### 4.3 Deferred, with the reason

#202 and #306 (Griffin — one family); #262 (gated on #349); #218–#221 (Boolean/SAT — formulation work
first); #269 (Rule 2); #69, #86–#89, #225 (no named workload).

**#202's board row was reset from In Progress to Todo.** Its lease was stale, `zb-claim.sh state 202`
returned `stale`, and no open PR referenced it. The row was claiming work nobody was doing.

### 4.4 Shared code areas that make concurrent implementation unsafe

M25 named `src/grobner/f4/`, `src/linalg/` and `src/fields/`. M26 adds two:

- `src/grobner/research/resultant.rs` — M26-A only.
- the FGLM conversion path — M26-B only.

`src/grobner/f4/` is touched by **both** M26-C (#304, #322) and, conditionally, #268 and #330. Those
are sequenced within one workstream and one checkout, not parallelized. See §6.

---

## 5. Workstreams

### 5.1 M26-0 — the deciding measurements

**Issues:** #349, #348, #318, #319.

Four measurements, none of them expensive, three of which gate work elsewhere. #349 is roughly one
normal F4 run plus profiling overhead and it decides how M26-C is scoped. #318 and #319 bound every
ratio the milestone will quote, which makes them prerequisites of M26-A's re-costing rather than
loose ends.

This workstream gates **only** the F4 optimization program. M26-A and M26-B start immediately.

### 5.2 M26-A — asymptotic elimination, and the row it unblocks

**Issues:** #350, #351, #297, #367.

The claim in one line: `Res(f, g) = det Syl(f, g)`, but taking that determinant costs `O(n³)` where
driving `f mod g` down the remainder sequence costs `O(n²)`, and at the Sylvester order the six-round
rows use that is **1 692x measured** — 1.343 ms against dense LU's 2.272 s at degree 729, order
1 458, one pinned core.

Three things make the figure admissible rather than an artefact:

1. The dense baseline cross-checks **#312's independent single-worker figure** — 2.272 s against
   2.404 s, **5.5% apart**, different binary and different core.
2. Agreement against `Matrix::determinant` is asserted at every size.
3. The headline survived a correction: a measurement crate outside the worktree **silently lost
   `-C target-cpu=x86-64-v3`** because it does not inherit `.cargo/config.toml`, moving the figure
   **1 930x → 1 692x**. Both runs are kept. This is M25's measurement-integrity defect #8 and the
   only one of the six with no trigger to avoid.

**What exists and what does not.** The prototype was a throwaway crate outside `src/`, and
`research/m25-euclidean-resultant` carries **documentation commits only** — it is merged, and there is
no remainder-sequence implementation in `src/`. **M26-A is an implementation, not an integration**,
and the recommendation that described it as the latter was wrong about the state of the tree.

**The correctness problem is the whole of the work.** Specialization points where leading coefficients
vanish and the univariate degrees drop. The prototype carries a formal-degree correction; it has never
run inside the full pipeline. Differential tests against the existing determinant at every size are
the acceptance condition, not a nicety.

**Why this reverses §13.9's ranking, stated so the reversal is auditable.** §13.9 ranked harder
resultants below conversion on the grounds that "the baseline is now measurably clean, so there is no
implementation slack to recover." That judgement is about **#297's axis 1**, which is close to
zero-sum against a sweep already 92–95% efficient. Axis 4 is a different axis, it is asymptotic rather
than constant, and the M25 reconciliation table recommends **"build axis 4 only"** on the strength of
the 1 692x. §8.4.2's "what would change this decision" names two honest routes — an owner
authorization at ~3 h, or an asymptotic improvement from #297 — and **axis 4 is the second route.**
The row needs ~1.3x and receives ~3x.

### 5.3 M26-B — competitive order conversion, as parity

**Issues:** #58, #224, #323, #368.

The deficit is real, measured, and the larger of the two. The staging is in #368: characterize before
implementing, one bounded prototype rather than every sparse-FGLM variant, certify against the
existing `O(N·D)` verification, then benchmark against msolve with operator construction reported
separately from conversion.

**The framing is parity, and this is a correction to the recommendation this plan came from.** That
document presented the ~30x as the largest competitive lever and left the frontier implication open.
#323 closes it: at Anemoi `N = 6`, **F4 refused before FGLM was ever reached**, over its entry budget
by **112 entries in 20 million** — one part in 180 000. The FGLM budgets are the second gate. The
route to the next Anemoi rung therefore runs through **#322's knob coupling in M26-C**, not through
this workstream.

So M26-B is funded for competitive parity and for a more general zero-dimensional capability —
conversion is shared by MQ solving, Anemoi, MinRank formulations and anything else needing a lex basis
from a degrevlex one. **It is not funded as frontier extension, and no M26 report may present it as
such while #323 stands.**

Stage 1 can refuse the rest of the workstream, and that negative result is a deliverable.

### 5.4 M26-C — foundational F4, two unconditional and two gated

**Issues:** #304, #322 unconditional; #268, #330 conditional on #349.

#304 is the one foundational improvement worth doing regardless of the profile: after #305 reduced the
symbolic preprocessing queue by 9.06x, the next major peak allocation became the **basis itself**,
retained in multiple representations during final reduction. That is a measured mechanism, not a
general claim about locality.

#322 is promoted from a budget bug to a frontier item by #323. If one part in 180 000 over the entry
budget is what refused Anemoi `N = 6`, then a knob whose effective limit is
`min(max_live_nonzeros, max_live_bytes / 16)` — so that lifting one knob does nothing — is the thing
standing between the current board and the next rung.

#268 and #330 are **promoted only if #349 implicates their stages.** #268's two target stages have
Amdahl ceilings of 2.59x and 1.92x, the right order to span 4.11x if both contribute, but those
ceilings come from katsura and cyclic while the losing instance's split is unprofiled. If the profile
confirms them, #268 becomes the rare H-series item surviving the screen on **external** evidence.

**Both objectives are measured and reported separately:** the gap against Singular, and the maximum
tractable MQ size. An optimization that saves memory while leaving the resource stop unchanged is
useful and is **not** reported as a frontier extension — M25's #305 is the precedent.

### 5.5 M26-I — integration, scoreboards, and the report

**Issues:** #256, #339, #369, #370.

#369 is the cheapest high-value item in the milestone: three adapters, zero retained records, and a
protocol already frozen. #339 matters more with parallel implementation agents than it did in M25,
where individually green PRs produced an invalid combined state.

---

## 6. Agent ownership boundaries

One writer per checkout, each on a real `git worktree` and its own branch.
`Agent(..., isolation: "worktree")` is not a reliable guarantee of file isolation for concurrent
writers.

| agent | worktree | branch | issues | primary files |
|---|---|---|---|---|
| RESULTANT | `zb-m26-resultant` | `feat/m26-euclidean-resultant` | #350 #351 #297 #367 | `src/grobner/research/resultant.rs`, `univariate_cico.rs`, `examples/resultant_cico.rs`, `docs/research/structured-sylvester.md` |
| FGLM | `zb-m26-fglm` | `feat/m26-krylov-conversion` | #58 #224 #323 #368 | the FGLM conversion path, `src/linalg/**` Krylov additions, `docs/research/anemoi.md` |
| F4 | `zb-m26-f4` | `perf/m26-f4-foundations` | #304 #322, then #268 #330 | `src/grobner/f4/**` |
| PROFILE | `zb-m26-profile` | `perf/m26-stage-profile` | #349 #348 #318 #319 | profiling harness, `docs/research/f4-resource-scaling.md` |
| integration | orchestrator checkout | — | #256 #339 #369 #370 | **this document**, `README.md`, scoreboard regeneration, runner contracts |

**No workstream agent edits this document.** Research documentation is written independently and
integrated later.

**The one unsafe overlap is `src/grobner/f4/`**, wanted by F4 (#304, #322) and conditionally by #268
and #330. All four are sequenced inside the F4 checkout. PROFILE reads F4 but writes only the
harness. After any parallel run, `git status` the orchestrator checkout and confirm no agent touched
files outside its scope.

Claims follow `CLAUDE.md`: claim before writing code, open a draft PR early with `Closes #NNN` as the
heartbeat, release on finish or abandon.

---

## 7. Experimental baselines

### 7.1 Hardware, recorded because every figure depends on it

AMD Ryzen Threadripper PRO 5995WX, 64 cores / 128 threads, 1 socket, L3 256 MiB across 8 instances,
503 GB RAM. Fedora, Linux 7.2.10. Measured figures record `ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY`.

### 7.2 Protocol

M25's protocol is inherited unchanged and may not be weakened:

- **Serialize benchmarks on the lock.** `tools/benchlock.sh`, plus per-agent target *and* scratch
  directories. A clobbered `tee` is a silently wrong figure.
- **Timings on the lock; peaks may be taken off it**, per `f4-resource-scaling.md:277`.
- **`tools/rss-guard.sh` for runs with material allocation risk.** Never find a measured binary with
  `pgrep -f` — a heredoc script's own text is in its wrapper's cmdline, so the pattern matches the
  wrapper (#328). Background the binary directly: `taskset` execs and keeps the pid, `timeout` forks
  and does not.
- **Build flags are verified, not assumed.** A measurement crate outside the worktree does not
  inherit `.cargo/config.toml`. This has cost this repository three sets of figures.
- **Startup floor and task equivalence** on every cross-library row.

### 7.3 Stage-level attribution, and what it may be called

A stage share is a share. It may be called a ceiling under Amdahl and it may **never** be called a
speedup. Any end-to-end claim is measured end to end.

---

## 8. Research gates

### 8.1 Gate M26-0 — the profile decides, and it is cheap

#349 runs **before** M26-C commits to anything beyond #304 and #322.

| measured bottleneck | consequence |
|---|---|
| interreduction and matrix construction dominate | #268 and #330 promoted; compact representations funded on external evidence |
| elimination dominates | Rule 2 is challenged on an external instance for the first time; #269 and #262 reconsidered, but only with the Amdahl arithmetic redone |
| neither explains most of the 4.11x | #268 ruled out; the residual becomes its own issue, and M26-B is the better investment |

#318 and #319 resolve or are explicitly bounded **before** M26-A re-costs `rf4-rp2`.

#### 8.1.1 Answered, and the gate as written was slightly wrong

**#349 is done (PR #393), and the answer is interreduction at 80.4%.** On `mq-random-10` at the
recorded digest, under `F4Options::default()` because that is what the record used, over four runs
with identical pairs, batches and basis:

| stage | share | ceiling if free | against the measured 4.13x |
|---|---:|---:|---|
| symbolic | 1.4% | — | — |
| construction | 3.5% | — | — |
| **#268**, symbolic + construction | **4.9%** | **1.05x** | **cannot explain it** |
| **#269**, elimination | **13.9%** | **1.16x** | **cannot explain it** |
| **#304**, interreduction | **80.4%** | **5.10x** | **spans it** |

So **#268 is ruled out on external evidence** — the reversal of what §13.9 expected, which was that
this profile would give it the first external support any H-series item had — and **#304 is promoted
to High**, now the F4 priority rather than only a memory finding.

**The table above this one conflated two stages that point at different issues.** Its first row
reads "interreduction and matrix construction dominate → #268 and #330 promoted", but #268 targets
symbolic and construction while #304 targets interreduction, so the row bundled an outcome with a
consequence that does not follow from it. The measured outcome — interreduction dominating and
construction at 3.5% — promotes #304 and **rules #268 out**, which is nearer the third row than the
first. The gate still decided the question; it would have mis-stated the answer if read literally,
and a gate that can do that is written badly. The lesson for the remaining gates is to key each
branch to the **issue** a stage implicates, never to a stage name.

**#330 is not promoted.** It targets column indexing during symbolic preprocessing and matrix
construction, which together are 4.9% here. It stays deferred on the same evidence as #268.

**A second finding, outside the gate.** Under `F4Options::baseline()` this instance does not finish,
refusing at 20 000 277 live nonzero entries against the shared 20 000 000 budget. That is the second
unrelated workload to cross #322's coupled limit by one part in 10^5, after Anemoi `N = 6` (#323),
and it strengthens #322's promotion in §5.4 rather than changing it.

### 8.2 Gate M26-A — the correctness problem before the speedup

1. Differential agreement against `Matrix::determinant` at every size, including specialization points
   where leading coefficients vanish and degrees drop. **No performance figure is quoted before this
   passes in the full pipeline.**
2. #351's root-finding measurement at the relevant degree, distinguishing **finding one usable root**
   from **enumerating all roots**. The existing `roots()` against a verified Graeffe route.
3. Then and only then, the `rf4-rp2` re-costing of #367, every term measured, the ~20% systematic
   removed or carried as a band.
4. Then the owner's explicit go/no-go, **recorded before launch.** §8.4 requires the cost stated and
   the decision taken before execution, and a row whose margin was minutes cannot be authorized on an
   extrapolated term.

### 8.3 Gate M26-B — stage 1 can end the workstream

The 82.8% lex-walk-and-dependence-test split must reproduce on a second Anemoi rung. If it does not,
the family is not a candidate, no prototype is built, and the characterization is the deliverable.
Operator sparsity and shape position are measured in the same pass.

### 8.4 Gate M26-C — #304 and #322 proceed; #268 and #330 wait

#304 and #322 are measured mechanisms and need no gate beyond ordinary review. #268 and #330 are
unfunded until §8.1 returns.

### 8.5 Gate M26-I — the protocol is not weakened to fill the board

**#395 lands before #369.** Populating Scoreboard A means setting wall limits on rows that may not
finish, and `competitive_sweep.rs` relies on a cooperative stop *returning* with its statistics. A
limit that is not honored is worse than no limit, because the row is then recorded as a completed
comparison rather than as a resource stop. No retained record is affected — all 72 carry no time-stop
marker — so this is a gate on new records rather than a correction to old ones.

Adding records will add startup-floor disqualifications. They are reported, never dropped. A ratio
against a tool that could not accept the input is not recorded.

---

## 9. Resource budgets

- Ordinary benchmarks: short, modest, on the lock.
- Longer experiments require a documented cost estimate before launch.
- **Any run projected to exceed ~2 h wall or ~64 GB peak RSS requires explicit owner authorization.**
- Never an unbounded computation because a predictor suggests it might finish.
- An external watchdog even where an internal time budget exists.
- A run whose actual growth violates its approved ceiling is terminated.

**Authorized at the time of writing:** #349's profiled F4 run on `mq-random-10`; #351's root-finding
measurement; #350's differential and benchmark suite at orders through 1 458; M26-B stage 1's Anemoi
rung profile.

**Not authorized without a fresh decision:** `rf4-rp2` (#367) — carried from M25 §9 unchanged, now at
**1.70–1.88 h against the ~2 h ceiling** with root finding still the unpriced term. `rf6-rp0`
(16.15 h), every eight-round row (`rf4-rp4` ≥490.5 d), and any Anemoi rung past `N = 6`.

**The standing ceiling is not raised for M26.** #367's route to authorization is a measured re-costing
plus an owner decision, not a larger ceiling.

---

## 10. Acceptance criteria

**Minimum.** The Euclidean remainder sequence landed in `src/` and independently validated against the
existing determinant, including at specialization points; #349's stage profile completed and acted on;
#351's root-finding cost measured; M26-B stage 1's characterization recorded whether or not it
supports continuing; #304's duplicated basis storage removed with measured peak RSS before and after;
Scoreboard A holding retained records for ≥3 libraries beyond Zeebra, or a documented per-library
blocker; #318/#319 resolved or explicitly bounded; the board and documentation truthful.

**Strong.** The minimum, plus a verified witness on a harder Poseidon **parameter combination**
(#367), or a recorded refusal naming the measured term that refused it; **and** a meaningful
end-to-end conversion improvement against the M25 baseline — 3–5x is substantial; **and** #322
resolved such that the Anemoi `N = 6` entry-budget refusal is understood and the next rung is costed.

**Stretch.** Conversion within roughly **2x of msolve** on a representative nontrivial workload, at
equivalent concurrency, with measured memory and no startup-floor distortion; **or** a verified
cryptanalytic result beyond M25's measured frontier; **or** a clear same-machine lead on a
representative computer algebra task, full correct computation, task-equivalent.

**A kernel-level win alone does not satisfy the stretch criterion.** 1 692x on a stage is not a
stretch result; ~3x on the row, delivered end to end and verified, is a Strong one.

---

## 11. What M26 will not claim

- That 1 692x on the determinant stage is 1 692x on anything a user runs. It is **~3x on the row**,
  and after axis 4 the route is 78% root finding.
- That a harder parameter combination is a larger round count. The cryptanalysis scoreboard records
  these separately. Both are legitimate; they are different mathematical achievements.
- That closing the conversion gap extends the Anemoi frontier, while #323 stands and F4's entry budget
  is the first gate.
- That sparse-FGLM would be 30x faster. The three engines reach a lex basis by three different
  algorithms; `MILESTONE-FGLM-SCALABILITY.md` §8.5's measurements against that claim stand unrefuted.
- That a memory reduction is a frontier extension, unless the resource stop actually moved.
- A speedup ratio against a tool that could not accept the input, or that computed a different object.
- Any ratio computed across the #318/#319 boundary without its ~20% systematic stated.

---

## 12. Future-work register

| item | why it is not in M26 | what would schedule it |
|---|---|---|
| Griffin/FreeLunch (#202, #306) | Buys one family. The strongest speculative direction — its central idea, that a suitable representation makes an expensive algebraic computation unnecessary, is the shape of Zeebra's own F4-to-resultants win | A generalization beyond one family, or a published witness it uniquely reaches |
| Boolean/SAT (#218–#221) | Characteristic-two formulation work and a fair SAT comparison come first. #272 notes `GF(2)` is profilable today | A defined key-recovery workload and a comparison protocol that survives review |
| MinRank | No smallest credible target; formulation cost unestimated | A named instance with a published comparand |
| F4 matrix corpus (#262) | Rule 2 | #349 implicating elimination |
| GPU / out-of-core (#69, #86–#89, #225) | No named kernel, workload, predicted benefit, benchmark. #305 removed the main argument | All four, per §3 |
| `rf6-rp0` and eight-round rows | 16.15 h / ≥490.5 d. Not reachable by a constant | Sub-quadratic root finding **and** sub-quadratic interpolation **and** #243-class build work — four walls, three of them serial quadratic stages |
| Poseidon Initiative Attack Reward Program | Requires a public ePrint paper by end of 2026 and an improvement to published attacks. **A faster implementation of an established algorithm does not qualify** | A genuinely better attack formulation or elimination strategy, evaluated on its own merits. Tracked separately from M26's engineering criteria and **not** a dependency of any of them |

---

## 13. Reproducing

```bash
# the claim queue, before picking anything up
./scripts/agent/zb-claim.sh orient

# the existing F4 stage profiler, which is where #349 starts
cargo run --release --example f4_profile -- list
cargo run --release --example f4_profile -- baseline
```

**#349 is work, not a command.** `f4_profile` takes a *configuration* name and profiles the built-in
benchmark systems; `mq-random-10` is an **external corpus** instance
(`src/grobner/external/corpus.rs:152`, `random_mq_instance(10, 10, …)`) and the profiler has no path
to it. Reaching the losing instance's stage split is the deliverable.

```bash
# the dense Sylvester baseline #350 must beat, and the measurement #318/#319
# are about. On the lock, one pinned core, build flags verified not assumed
./tools/benchlock.sh -- taskset -c 0 \
  cargo run --release --example determinant_sweep -- --order 1458 --determinants 128
cargo run --release --example determinant_sweep -- --concurrency 32   # the width penalty, #319

# root finding's comparand (#351) — one usable root is not all roots
cargo run --release --example graeffe_root -- list
cargo run --release --example graeffe_root -- koalabear degrees=6561,19683

# the conversion split M26-B stage 1 must reproduce on a second Anemoi rung
cargo run --release --example fglm_profile -- katsura-7
cargo run --release --example anemoi_ladder

# the competitive board (#369). `competitive` only renders accumulated history
# and takes no measurements; tools/scoreboard.sh takes them, by tier
cargo run --release --example competitive                 # render to stdout
cargo run --release --example competitive -- --write      # update research/competitive/
ZEEBRA_MACHINE=... ZEEBRA_AFFINITY=... ./tools/scoreboard.sh stable --write

# the agent tooling's own tests
bash scripts/agent/test/zb-claim-test.sh
bash tools/test/rss-guard-test.sh
```

`ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY` must be set or the records key wrong, and `--all` is never
passed. Commands are as of writing; `docs/guide/benchmarking.md` is authoritative for example
invocations.
