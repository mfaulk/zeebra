# Benchmarking and measurement

The benchmark suites, the examples that report algorithmic counters, and the rules this repository
follows before publishing a number.

## Measuring on a busy machine

For the cached monomial degree and packed order-key experiments, see the
[stage gate and reproduction commands](../research/monomial-degree.md). Build
`monomial_degree_profile` for a single-fixture stage/RSS report with the full basis on stdout,
or `monomial_packing` for the comparison-loop experiment. The cache was rejected for production;
the retained patch reproduces the measured cached arm without changing the public representation.

`tools/benchlock.sh` runs one command at a time, machine-wide, and records that it did:

```sh
tools/benchlock.sh <owner-tag> <command> [args...]

tools/benchlock.sh agentD cargo run --release --example univariate_scaling -- koalabear
```

Two concurrent measurements on one box contend for shared cache and memory bandwidth, so a ratio
taken while something else ran is not a measurement of the change. The script takes an exclusive
`flock`, appends `QUEUED` / `START` / `END` lines with the owner tag and a timestamp to
`$HOME/.zeebra/benchlock.log` (override the directory with `ZEEBRA_BENCHLOCK_DIR`; it must be
outside every worktree), and exits with the command's status so a failing measurement fails the
caller. Two records whose `START`..`END` windows overlap were not taken under this protocol, and
the log is what says so — which is what makes figures taken weeks apart, such as the pre- and
post-#161 revisions in [`docs/research/graeffe-root-finding.md`](../research/graeffe-root-finding.md)
§4.4, comparable with each other.

The lock handles contention and nothing else. Also needed, per invocation:

- `CARGO_TARGET_DIR` inside the caller's own worktree and `RUSTC_WRAPPER=""`. The default target directory is keyed by package and profile rather than
  by checkout, so two worktrees overwrite each other's `libzeebra.rlib` and an example links
  against a library built from other source; the symptom is a missing export that is plainly
  present.
- A private scratch directory. Two callers' `tee run1.txt` collide, and a clobbered `tee` is a
  silently wrong figure rather than a crash.
- `timeout --signal=INT --kill-after=60s` on anything long, with a budget-killed run reported as a
  resource-limited result rather than as a measurement. A run left past its budget holds the lock
  against everyone else.
- A memory ceiling enforced by `tools/rss-guard.sh`, not by a hand-rolled `pgrep -f` loop. See
  below.
- **`setsid`, so the run survives its launcher.** See *Why a run ended* below.
- A build whose ISA floor actually survived. `.cargo/config.toml` is not inherited by a harness
  crate built outside this worktree, which is a third route to losing `-C target-cpu=x86-64-v3`
  with no `RUSTFLAGS` mistake to avoid (#352); `tools/benchlock.sh` lists it among the hazards the
  lock does not handle.

### Why a run ended

An `END` line names its cause, and **`end=exited` rather than `status=0` is what says a measurement
completed**. The distinction is not decorative. A 1.5-hour Anemoi run was killed at 3 177 s of a
5 400 s budget when the agent harness stopped the background shell that had launched it — taking
`benchlock`, `timeout`, `taskset` and the binary with it, since all four were its descendants — and
the log recorded:

```text
2026-11-06T20:01:47-05:00  END  zb-m25-anemoi  pid=2761621  status=0  elapsed=3177s  ...
```

`status=0`, a plausible `elapsed`, and no resource limit anywhere near being crossed. From the
lock's side the measurement had finished; the only clue otherwise was an output file holding eleven
header lines and no stage table. That consumed 53 minutes of a serialized mutex with three other
agents queued behind it *while reporting success*, and it made every historical `END status=0`
retroactively ambiguous — which matters because the resource policy authorizes bounded runs on the
grounds that a budget stop is observable and attributable, and it is not, if a budget stop and an
unrelated kill read the same (#344).

So the cause is now explicit:

| field | meaning |
|---|---|
| `end=exited` | the command ran and returned on its own; `status=` is its own status |
| `end=budget` | status 124, GNU `timeout`'s convention — a resource-attributed stop |
| `end=signalled-child(NAME)` | the command itself died of a signal; `status=` is 128+n |
| `end=launcher-signal(NAME)` | **the lock itself was signalled.** `status=` is forced to 128+n however the command exited, and `child=` keeps the command's own status visible |
| `launcher=gone` | the run outlived the process that launched it |
| `end=aborted`, `route=trap` | the `END` came from the `EXIT` trap, so the lock never reached its own last line and never observed the command return. Never `end=exited`, and `status=` is 128 rather than 0 |

`end=launcher-signal` is the one that closes the incident, and the override is the point: in that
run the child reported **0**, because an intermediate `bash run.sh` with no `set -e` exited on its
own last command after the binary beneath it had died. No exit status reaching the lock could have
been trusted, so a signal to the lock now outranks whatever the command said.

Two cases leave no `END` at all, both honestly. A signal arriving while a caller is still
**queued** leaves a `QUEUED` line and nothing else, which is right: no `START` means no window was
opened, so nothing later can look like it overlapped. And `kill -9` cannot be trapped, so it leaves
a `START` with no `END` — an unterminated window, unhelpful but not a claim that anything finished,
and the one case no script can prevent. Verified by process-group kill:

```text
kill -TERM  ->  status=143 end=launcher-signal(TERM) child=143
kill -HUP   ->  status=129 end=launcher-signal(HUP)  child=129
kill -USR1  ->  status=138 end=launcher-signal(USR1) child=138
kill -KILL  ->  (no END line)
```

`launcher=gone` is a note and not a failure, deliberately — `setsid` reparents a run to init on
purpose, so overriding the status on it would fail the very discipline being recommended:

```sh
setsid nohup bash run.sh > log 2>&1 < /dev/null &
ps -o pid=,sid= -p "$!"   # a session id that differs from this shell's is the confirmation
```

The lock does **not** call `setsid` itself. A detached run that nobody can cancel is its own
hazard, and that trade is worse than the one it would fix; so the lock records what happened rather
than preventing it.

`tools/test/benchlock-test.sh` covers the classification and reproduces the incident end to end —
benchlock in its own session, a measured command whose wrapper swallows the kill and exits 0, and a
signal to the whole process group — asserting that the resulting `END` is not `status=0`. It runs
in CI's `agent-scripts` job, in a throwaway `ZEEBRA_BENCHLOCK_DIR`, so it never takes the real lock
or appends to the real log.

### Enforcing a memory ceiling

```sh
tools/rss-guard.sh <comm> <id-substring> <ceiling-kb> [--poll <seconds>] [--once] [--wait <seconds>]
                   [--signal <name>] [--kill-pid <pid>] [--dry-run]

tools/rss-guard.sh anemoi_ladder anemoi17-cico-n6-fcico $((16 * 1024 * 1024)) --poll 10
```

`<comm>` is the binary's name as `/proc/<pid>/comm` spells it, truncated to 15 characters by the
kernel and by the script alike; `<id-substring>` is then confirmed against that pid's command line,
so a second concurrent run of the same binary on a different row is not watched. The mark read is
`VmHWM`, the high-water mark, so a peak that has already been released still counts.

**Do not find the process with `pgrep -f`.** A script created and run through a heredoc inside
`bash -c` — how agent sessions launch benchmark runs — has its entire text in the wrapper's
`/proc/<pid>/cmdline`, and `pgrep -f` matches the full command line, so it matches the wrapper on
its own payload. Observed live in #328 while one row was running and the next was still queued:
`pgrep -f` returned two `comm=bash` pids for the queued job and did not return the running binary
at all. The consequences were a monitor reporting queued work as running, and an RSS guard reading
a wrapper's ~4 MB high-water mark — which can never exceed a 16 GiB ceiling, so it silently never
fired and the run proceeded unsupervised while looking supervised.

Hence the exit statuses, which split three ways rather than two:

| status | meaning |
|---|---|
| 0 | watched to completion, the ceiling was never crossed |
| 3 | the ceiling was crossed and the signal was sent |
| 1 | **nothing matched — nothing was guarded.** Not a pass |
| 2 | a read of `/proc` failed |
| 64 | usage error, including a `<comm>` that names a wrapper (`bash`, `timeout`, `taskset`, …) |

Status 1 is the one worth the separate code: "watched and it was fine" and "watched nothing" are
the same output otherwise, and only the first is a guarded run. A guard started before its binary
waits `--wait` seconds (60 by default) for one to appear and then reports `NOT GUARDED` rather than
polling an empty process table forever.

When the launcher and the guard are in the same script, prefer neither form of matching: capture
the pid from `$!` and pass it with `--kill-pid`.

`tools/test/rss-guard-test.sh` covers the pure half against a synthetic `/proc` — including a case
where both wrappers' command lines contain the row id and only the binary is matched — and runs in
CI's `agent-scripts` job.

## Which commit a figure came from

A measurement published under `docs/` states the commit it was taken at. The field has always
existed — `Environment::commit` (`grobner::record`), filled from `git rev-parse` — and the
gap was the prose, which recorded the machine, the pinning, the build flags and the lock and never
the commit (#335). The cost was concrete: #318 found a figure on record 1.2x faster than the same
measurement taken later, and "re-measure at the old commit" could not be *set up* from what was
written down.

So every document under `docs/research/` and `docs/MILESTONE-*.md` that contains a timing or memory
figure in a table carries a declaration in its header:

```text
**Measured at:** `93bb1c2`                    the commit the figures were taken at
**Measured at:** publication bound `x`…`y`    retrospective: at or before the commits that published them
**Measured at:** not measured here — <why>    every figure is quoted from a cited source
**Measured at:** unrecorded — <why>           genuinely unrecoverable, and said so
```

```sh
tools/check-measurement-provenance.sh            # all of docs/; rc 1 = a document with no era
tools/check-measurement-provenance.sh docs/research/f4-resource-scaling.md
```

The checker runs in CI's `agent-scripts` job. It exists rather than a convention because the M27
reproducibility checklist already asked for the commit and the documents still did not carry one.

A figure already published without its commit can usually be dated from git, which is where the
existing `publication bound` declarations came from:

```sh
git log -S "37 634.3" --format='%h %ad' --date=short -- docs/research/resultant-elimination.md | tail -1
```

That is an upper bound, not the measured tree, and it is labelled as one — never written into
`Environment::commit`, whose contract is the commit the run actually used. A commit is also not by
itself reproducibility: §6.5's figure does not reproduce at its own commit, because the session and
the ambient load moved it more than any code did, which is why `tools/benchlock.sh` records `load=`.
`docs/research/external-comparison-protocol.md` §10 is the authority on all of this.

## Benchmarks

Criterion benchmarks cover field arithmetic, sparse polynomial operations, dense and sparse linear
algebra, and Gröbner basis computation:

```sh
cargo bench                              # everything
cargo bench --bench grobner              # one suite
cargo bench --bench sparse_linear_algebra
cargo bench --bench f4_stages
cargo bench --bench f4_matrix_corpus     # elimination, one pinned real Macaulay matrix at a time
cargo bench --bench fglm                 # order conversion: stages, pipeline, strategies,
                                         # dependence, the shipped configuration, verification
cargo bench --bench polynomial_solving   # one solution against all of them, both routes
cargo bench --bench sparse_polynomial    # multivariate arithmetic, four arities
cargo bench --bench monomial_order       # MonomialOrder::cmp, three arms, two tie regimes
cargo bench --bench pow_strategy         # FiniteField::pow's body, five arms, six exponent widths
```

`monomial_order` is #317's gate rather than a coverage benchmark, and it has **three** arms where an
A/B would have two. It prices one change — storing a monomial's total degree instead of summing
`[u32; N]` on every graded comparison — and a two-arm first cut reported `lex` at 3.32x, on an order
that never reads the degree. So `production` is `MonomialOrder::cmp` on the real `Monomial<N>`,
`summed` is a bench-local transcription of it, and `stored` is that transcription with the degree in
a field; `summed` against `production` is the fidelity check, and the `lex` rows of `summed` against
`stored` are the control. See `docs/research/interreduction-cost.md` §3f.

`pow_strategy` is #181's gate, and the same shape for the same reason: `production` is
`FiniteField::pow` as shipped and the other four arms are bench-local transcriptions of the bodies
it could have — the recursive one it had, and three loops. It needs that many because the obvious
two-arm A/B gives the wrong answer. Making the default iterative is **1.9x** at the exponent widths
`PowerPermutation::invert` uses and a **9x to 40x regression** at `pow(1)` over a field whose
multiply is expensive, in the same change, because the loop seeds its accumulator with one and so
pays a multiplication the recursion does not. So `pow_limbs` walks the exponent downward below
`NARROW_EXPONENT_BITS` and upward above it, and `production` tracking whichever arm the threshold
selects is the fidelity check. `e8` and `e16` are in no call site and exist only to bracket the
threshold's crossover, which turns out to be field-dependent. Four arms also caught a candidate
that should have won on operation count and did not — `seeded` — which is the reason the arm
exists. See `docs/MILESTONE-LARGE-PRIME-FIELDS.md` §4.1.2.

`sparse_polynomial`'s `mul_dense` arm is separate from `mul` because they are different shapes, not
just different sizes. `mul` draws monomials independently, which is sparse in the total-degree sense
at every size; `mul_dense` builds the dense total-degree simplex, which is what the symbolic
resultant build actually produces and what selects the specialised bivariate multiplication route.
An arm of only the first kind cannot catch a wrong dispatch predicate.

`sparse_linear_algebra` has three groups, and the differences between them matter. `sparse_linalg`
times sparse row echelon beside dense *reduced* row echelon, which performs a back-substitution
pass the sparse side never does; it is indicative of nothing about storage and is kept only for
continuity. `matched_echelon` runs the identical algorithm under each `linalg::echelon` backend on
identical matrices, and times densification and sparsification in their own benchmark, so the
comparison measures representation rather than algorithm or conversion. `sparse_rref` times
`linalg::sparse::reduced_row_echelon`, whose back-substitution pass neither of the others covers,
on two shapes that answer different questions: a random square matrix, which at low density fills
in until it is near-dense and leaves the pass nothing to skip, and a banded matrix, which stays
sparse throughout and is where skipping is worth anything.

`f4_stages` times F4's stages separately — symbolic preprocessing, matrix construction,
elimination under each backend, representation conversion, and a whole batch — replaying the
batches a real computation produced rather than synthetic ones. `grobner` says whether something
got faster; `f4_stages` says whether a change removed cost or moved it from one stage to another.

`f4_matrix_corpus` is the per-matrix complement to it. `f4_stages` sums elimination over every batch
of four instances over one field under `F4Options::baseline()`, which is the right unit for "did the
stage get faster" and the wrong one for "which kernel is faster on which matrix": the shapes are
summed over, the field is fixed, and `baseline()` builds matrices the shipping default never builds.
This benchmark times **one named matrix at a time**, across six field types spanning five field
widths and three scaffolding regimes under both presets, with Criterion's throughput set from the matrix's nonzero count. Each
matrix is captured out of a live run through the `BatchObserver::matrix` hook — it is the object F4
handed to elimination, not a reconstruction — and is pinned by digest, so a benchmark here cannot
report a figure about a matrix that moved. See
[`docs/research/f4-matrix-corpus.md`](../research/f4-matrix-corpus.md).

Wall-clock time alone does not say *why* a Gröbner computation got faster. For the algorithmic
counters — pairs considered, pairs eliminated by Buchberger's first criterion, reductions, zero
reductions, basis size:

```sh
cargo run --release --example grobner_statistics   # Buchberger
cargo run --release --example f4_statistics        # F4, beside Buchberger
cargo run --release --example f4_profile           # F4, cost attributed per stage
cargo run --release --example f4_profile -- list   # the configurations available
cargo run --release --example f4_memory            # F4, memory attributed per structure
cargo run --release --example interreduce_working_set -- katsura-11 --arm unbounded
cargo run --release --example f4_degrees           # F4, work and useful work per degree
cargo run --release --example f4_schedule          # critical-pair order, and batch size, apart
cargo run --release --example f4_schedule -- list  # the instances available
cargo run --release --example hilbert_study         # the semiregular model against the measurement
cargo run --release --example hilbert_driven        # a predicted cap against a cap chosen without one
cargo run --release --example hilbert_driven -- list
cargo run --release --example m22_ablation          # every M22 strategy, one table per instance
cargo run --release --example m22_ablation -- list
cargo run --release --example f4_blocks            # F4, row arrangements of the Macaulay matrix
cargo run --release --example f4_matrix_corpus -- list     # the pinned matrix corpus
cargo run --release --example f4_matrix_corpus -- check    # capture it and verify every digest
cargo run --release --example f4_matrix_corpus -- pin      # re-derive the pinned table
cargo run --release --example f4_matrix_corpus -- predict  # does the corpus rank kernels as a run
cargo run --release --example f4_selection         # reducer selection and the reducer cache
cargo run --release --example elimination_density  # how dense an F4 matrix really is
cargo run --release --example accumulator_span     # whether a vectorizable inner loop is available
cargo run --release --example accumulator_span -- list
cargo run --release --example boolean_density      # what a GF(2) entry costs, at two field widths
cargo run --release --example boolean_density -- 6 8
cargo run --release --example pair_criteria        # what each pair criterion discards, F4
cargo run --release --example pair_criteria -- buchberger
cargo run --release --example certification_criteria  # what they discard from a certification pass
cargo run --release --example certification_criteria -- list
cargo run --release --example f4_ablation          # every configuration, one table
cargo run --release --example f4_milestone         # both engines, at matched and default criteria
cargo run --release --example fglm_baseline        # which systems are zero-dimensional, and what
                                                   # a lex basis costs against a grevlex one
cargo run --release --example fglm_baseline -- cyclic-6   # one system per process
cargo run --release --example fglm_operators      # how sparse the multiplication operators are
cargo run --release --example fglm_conversion      # the FGLM pipeline against direct lex F4
cargo run --release --example fglm_profile         # where a conversion's time and memory go
cargo run --release --example fglm_profile -- katsura-7   # one system per process
cargo run --release --example fglm_border          # what deduplicating the border is worth
cargo run --release --example fglm_parallel -- per-batch   # is the border reduction worth
cargo run --release --example fglm_parallel -- sweep       # parallelizing? one table each
cargo run --release --example fglm_storage         # operator representations, stored and applied
cargo run --release --example wiedemann_conversion # certified scalar route versus classical
cargo run --release --example fglm_shape           # shape position, and what that route would save
cargo run --release --example fglm_ablation        # every strategy combination, one table
cargo run --release --example fglm_ablation -- list
cargo run --release --example solve_one            # systems in, verified solutions out, both routes
cargo run --release --example solve_baseline       # both routes with resources and outcome class
cargo run --release --example solve_auto           # four policies against an offline best-of-two
cargo run --release --example specialize_slices    # seeded slices of an underdetermined system
cargo run --release --example field_width          # what a 4-byte field element is worth, per
cargo run --release --example field_width -- axpy  # arm: the kernel, a dense echelon, F4
cargo run --release --example univariate_scaling   # univariate cost and memory against degree
cargo run --release --example univariate_scaling -- list
cargo run --release --example ntt_access           # #591: is the NTT access-bound or
                                                   #   arithmetic-bound? Needs a quiet box
cargo run --release --example ntt_access -- goldilocks budget=30
cargo run --release --example ntt_access -- list
cargo run --release --example univariate_scaling -- points=250,500,1000,2000   # lagrange only, exact counts
cargo run --release --example karatsuba_crossover  # Karatsuba against schoolbook, per field width
cargo run --release --example karatsuba_crossover -- bn254
cargo run --release --example division_crossover   # Newton inversion against long division, per field width
cargo run --release --example division_crossover -- bn254
cargo run --release --example division_crossover -- all max_log=13
cargo run --release --example subproduct_crossover  # the subproduct tree against the quadratic forms
cargo run --release --example subproduct_crossover -- bn254
cargo run --release --example multiplication_dispatch  # schoolbook vs Karatsuba vs transform, and the crossings
cargo run --release --example multiplication_dispatch -- koalabear max_log=17
cargo run --release --example multivariate_mul     # multivariate multiply: time and live heap per route
cargo run --release --example multivariate_mul -- chunk         # block size sensitivity
cargo run --release --example multivariate_mul -- max_degree=90 # stop short of the six-round size
cargo run --release --example graeffe_root         # Graeffe root finding, stage by stage, against `roots`
cargo run --release --example graeffe_root -- deflate   # all roots by deflation, #351
cargo run --release --example graeffe_root -- list
cargo run --release --example graeffe_root -- goldilocks degrees=256,1024,4096   # where the method does not pay
cargo run --release --example batch_inversion      # batch inversion: routine, integration,
cargo run --release --example batch_inversion -- f4   # and the F4 headroom left alone
cargo run --release --example competitive          # render research/competitive/ from its history
cargo run --release --example competitive -- --write   # and update COMPETITIVE.md in place
cargo run --release --example competitive_sweep -- --list   # corpus x engines x tasks, exploratory
. tools/external/env.sh                            # REQUIRED FIRST, or the sweep sees one engine
tools/benchlock.sh runner cargo run --release --example competitive_sweep -- \
    --row katsura-6 --task reduced-grobner-basis --measure --write   # one measured row
tools/benchlock.sh runner cargo run --release --example competitive_sweep -- \
    --characteristic 32003 --row katsura-6 --task reduced-grobner-basis --measure --write
                                                   # the same rung at the corpus's other identity;
                                                   #   only a PUBLISHED characteristic is accepted
tools/benchlock.sh runner cargo run --release --example competitive_sweep -- \
    --row mq-random-10 --task reduced-grobner-basis \
    --interreduction matrix --measure --write      # a row under a non-default F4 route; the route
                                                   #   lands in the row's library_version, because
                                                   #   the commit does not determine it (#507)
cargo run --release --example interreduction_routes            # both interreduction routes per
                                                   #   ladder rung, interleaved in one process,
                                                   #   with the matrix route's own verdict
cargo run --release --example interreduction_routes -- --orders --wall 60 katsura-6
                                                   # the same rung under grevlex, grlex and lex —
                                                   #   where the two routes disagree (#507 §3e.2)
cargo run --release --example interreduction_repeats           # the division route's repeat rate:
                                                   #   reduction steps whose work an earlier
                                                   #   element's reduction already did (#569).
                                                   #   Counts, not durations — load-independent
cargo run --release --example interreduction_repeats -- katsura-6 --order lex
                                                   # the same on the one path the division route
                                                   #   still ships on under the default
tools/benchlock.sh agentD cargo bench              # anything measured, under the exclusive lock
cargo run --release --example determinant_sweep    # the Sylvester determinant cost law,
                                                   #   five matrix orders, fitted with residuals
cargo run --release --example determinant_sweep -- --cost-only   # what the sweep would cost
cargo run --release --example determinant_sweep -- --kernel euclidean   # the O(n^2) kernel
cargo run --release --example determinant_width    # the width sweep 1..32 and the kernel split,
                                                   #   every arm in one process (#412)
cargo run --release --example determinant_width -- --count-allocations   # calls per determinant
cargo run --release --example determinant_width -- --compare-kernels --order 162 --width 32
                                                   # dense and Euclidean, same samples and width
cargo run --release --example f4_profile -- mq     # the competitive MQ instance, per stage
cargo run --release --example f4_profile -- mq-instance   # that instance as canonical text
cargo run --release --example f4_profile -- divmask       # #331: the divisor-mask counters
cargo run --release --example f4_profile -- symbolic-split  # #585: what share of symbolic
                                                   #   preprocessing the divisor search is
cargo run --release --example f4_profile -- mq-rows      # #477: reduced row echelon per batch
cargo run --release --example f4_profile -- scatter       # #582: the row scatter, split four ways
cargo run --release --example f4_profile -- handles       # #621: handles against the hash read
cargo run --release --example column_sort_routes   # #583: the column sort, stable against unstable
timeout 900 cargo run --release --example buchberger_reach -- katsura-6 lex all
```

`solve_baseline` is M21-0's baseline: both routes on every corpus system, reporting what each
*cost* and which of the mathematically distinct outcomes it reached — a verified point, no
base-field point, an inconsistent ideal, a positive-dimensional ideal, or a crossed budget. It
takes about 30 seconds, nearly all of it katsura-7's direct-lex attempt failing. See
[`docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md`](../MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md)
§4 for the table and what it decided.

`f4_statistics` prints matrix dimensions, how many reductions each matrix absorbed, how much of
each matrix was reduction scaffolding, and how much elimination filled it in. It asserts that the
two engines agree wherever both can run. It pins itself to `F4Options::baseline()`, because its
columns are the ones `docs/MILESTONE-F4.md` §7.1 records and comparing against them needs that
configuration.

`f4_profile` prints where the time went: symbolic preprocessing, construction, elimination,
candidate extraction, and the final interreduction, with the remainder shown as `other` so an
unattributed cost cannot hide. It takes the name of a configuration — `baseline` by default,
`recommended` for what `F4Options::default()` is — so the effect of one optimization can be read
off against another's. The timing comes from
`F4Options::measure_stages`, which reads a clock four times per batch and is off by default. Three
modes take no configuration: `mq` is the digest-pinned `mq-random-10` stage split (#349),
`mq-instance` prints that instance's canonical text — field, order, variables and generators, the
bytes the identity digest is taken over — so an external engine's own counters can be taken on the
same ideal and compared against these columns, and `construction` splits the construction stage
four ways (#330): the distinct-monomial set, the column sort, the monomial-to-column map, and the
row scatter, then measures the current route against the one it replaced in one process on one
build. `docs/research/groebner-jl-gap.md` is what the `mq-instance` comparison produced;
`docs/research/msolve-implementation.md` §4.1 is what the `construction` split settled.

`scatter` goes one level further in (#582), because the `construction` split left the scatter at
89% of the stage and no counter had ever been inside it. Two of its four parts are clocked —
`scatter_rows`, the per-row loop, and `scatter_assemble`, `SparseMatrix::new` plus the
row-provenance copy. The other two, the multiplier shift and the per-term column lookup, are per
*term*, where `Instant::now()` costs more than the work it would time; they come from
`ScatterPrefix`, a **nested ablation** whose arms are prefixes of the real loop and whose adjacent
differences are one step's cost. The full arm is that loop verbatim, so the table prints it
beside the clocked `scatter_rows` as a control: if those two disagree, nothing beside them means
anything. Each arm carries a checksum that an emptied arm cannot produce
(`test_the_scatter_ablation_arms_do_the_scatters_work` pins each one to a quantity derived from the
built matrix), the arm order rotates per repetition, and each arm is min-reduced over its own runs.

Since #621 the loop those arms describe is **not** the shipping one, so the mode clocks
`MacaulayMatrix::build_hashed_scatter_for_benchmark` rather than `build_measured` and keeps
reporting what #582 reported. `handles` is the A/B between the two. Symbolic preprocessing interns
every shifted row monomial to deduplicate its own work queue, so it now assigns each a handle — an
index into a first-appearance arena — and `Preprocessed` carries the handle of every row term in one
flat vector. Construction inverts the column sort's permutation into an array keyed by handle, and
the scatter reads a column by indexed load: no monomial is formed and no hash is probed. Both arms
read the same `Preprocessed`, built once per batch outside the timing, and every pair of matrices is
asserted equal. The table's `entries/col` column is the ratio #621's kill criterion rested on,
because the per-entry lookup can be removed at most once per entry.

`column_sort_routes` is the smallest of these questions and the last of #583's: whether
construction's column sort should be stable. It replays a `recommended` trace, snapshots the column
vector each batch hands the sort — `preprocessed.monomials`, which is what construction itself
collects — and sorts the same snapshot both ways, interleaved with the arm order
rotated and each arm min-reduced. The arms assert **equal output** as well as timing it, because
stability can only matter where the comparator reports a tie and a figure for two different column
orders would mean nothing. `sort_unstable_by` wins on every instance tried, so it is what
`build_measured` now calls; `docs/research/msolve-implementation.md` §4.1 has the table and what it
decided about the rest of #583.

A third configuration-free mode answers a question rather than reporting a cost. `f4_profile --
divmask` is #331's counter-only experiment: `F4Options::measure_divmask` builds a 32-bit divisor
mask with thresholds calibrated from the input's own exponent range and replays every divisibility
test in symbolic preprocessing against it **after** the real answer is known, so nothing a mask
could get wrong can reach the basis — asserted element for element by
`test_the_probe_does_not_change_the_divisor_selected`. It reports the tests performed, how many
answered negative, and how many of those a mask would have settled without an exponent comparison,
which is 94%–97% on every instance tried. The run pays a second walk of the basis per divisor
lookup, so **its durations are not quotable**; the counters are exact and machine-independent,
which is the trade `count_interreduction` already makes. See
`docs/research/msolve-implementation.md` §4 H2 for the result and what it does and does not bound.

`f4_profile -- symbolic-split` is the other half of that question, and the half that settled it.
`divmask` counts the tests a mask would answer; `symbolic-split` prices them, by multiplying
`divisor_scan_steps` — exact, and free, because the shipped scan increments it once per
divisibility test — by a per-step cost taken from timing `MonicBasis::find_divisor_with` over a
real basis and dividing by the steps that same scan reports. It prints a **range**, because a
negative answer exits early and a positive one compares every variable, and it labels its own
output a projection rather than a measurement. The answer is a null result: the divisor search is
2.5%–4.7% of `symbolic` on three of four instances and 24%–30% on the fourth, which bounds even a
*free* mask at under 6% of one run and under 1% of the other three. §4 H2 has the table and why
#585's stage 2 was closed rather than built.

`f4_memory` is the same question for bytes rather than for time, and it exists because the answer
turned out not to be the matrix. It runs a tracking `#[global_allocator]` beside the solver's own
counters, measures each batch's symbolic preprocessing and matrix construction on the batches F4
really selected — including the batch that is **refused**, which no `F4Statistics` field describes —
and prints each named structure's share against the measured peak, on katsura-6, katsura-7 and
cyclic-6. After symbolic preprocessing succeeds, a construction refusal also prints the exact
row, column and entry demand, the entry allowance and its excess. These are construction counts;
they do not predict elimination fill-in or the process's peak RSS.

`interreduce_working_set` is that question for the *final interreduction*, which `f4_memory`'s
per-batch probe does not reach. It runs **one rung and one arm per process**, because peak resident
size is a per-process reading: `--arm unbounded` lifts the live-entry allowance so the matrix pass
runs to completion and reports its elimination's own high-water mark, `--arm default` is the shipped
allowance where that pass refuses and falls back, and `--arm division` is the comparand the memory
ratio is against. It is the instrument [#536](https://github.com/mfaulk/zeebra/issues/536) was
settled with; `docs/research/f4-resource-scaling.md` §12 has the table it produced.

`interreduction_repeats` asks a third question about the same stage, and it is a **count** rather
than a measurement: how much of the division route's work is work an earlier basis element's
reduction already did. It replays the basis entering the stage — the last traced batch's basis plus
that batch's candidates — and reports, per reduction step, whether the
`(quotient monomial, reducer leading monomial)` pair recurred and whether the reducer's tail was
unchanged, which is the only case a cache could have served. Two input arms per rung, with
`reduce_batch_rows` the only difference, because the input decides the stage. Because the output is
operation counts and not durations it is **exact, deterministic and load-independent**, so it needs
no interleaving and no quiet machine — it runs under `tools/benchlock.sh` out of politeness rather
than for validity. It settled [#569](https://github.com/mfaulk/zeebra/issues/569), the last
unadjudicated candidate mechanism from #436: the repeat rate is **98.57%** and the verdict is still
not to build the cache, for the reasons in `docs/research/interreduction-cost.md` §3i.

`f4_degrees` is M22-0's baseline: one table per system giving, for each lcm degree, the pairs
selected and discarded, the split of matrix rows into reducer scaffolding and pair halves, **the
rank the pair rows added on top of the reducer block**, the pair rows that added nothing, the
largest matrix, the elements extracted, and how many of those came out below the degree that found
them. It covers katsura-5 for calibration, then katsura-6, cyclic-5, cyclic-6 and a planted
eight-variable system.

`m22_ablation` is M22-I's: the whole M22 strategy matrix on one table per instance, over the
corpus of §11.2 — katsura-5/6/7, cyclic-5/6, a planted system, a nonradical ideal, a
positive-dimensional one. Every row's basis is **asserted** equal to the baseline's and certified, since a differing
basis is a defect and a column reporting one would bury it. `total ms` is solve plus certification,
which is the only figure a default decision may use. Variable order is held fixed at the generated
layout throughout — M22-E measured it at 1.6x–1.7x, which would otherwise be attributed to whichever
F4 strategy varied alongside it. There is no mutant row, because M22-D added no mutant mode; `D = A`
is printed to make the gap explicit. See
[`docs/MILESTONE-DEGREE-AWARE-F4.md`](../MILESTONE-DEGREE-AWARE-F4.md).

`hilbert_study` is M22-B's measurement: the exact Hilbert function of each computed basis's
leading-term ideal against the semiregular prediction, degree by degree, with the first
disagreement and its sign reported. It covers textbook regular sequences, random homogeneous
quadratics, deliberate counterexamples, the Fukuoka type III top forms *and* the published
inhomogeneous instances, and reduced-round Poseidon. See
[`docs/research/hilbert-functions.md`](../research/hilbert-functions.md) for the tables.

`f4_schedule` is M22-A's measurement: every compiled critical-pair order on one table per
instance, with the computed basis asserted equal to the baseline's on every row. Ordering and batch
sizing get a table each, deliberately — a sort and a cap varied together cannot be attributed —
plus a cross product on one instance to check whether the two interact. `-- list` names the
instances and `-- <name>` runs one per process.

`f4_blocks` replays the batches a computation really built and eliminates each one four ways —
rows as preprocessing produced them, reducer rows first, reducer rows taken as established pivots,
and the same with the reducer block interreduced — reporting row operations, peak live nonzeros,
final nonzeros, and time on the identical matrices. Holding the matrix fixed is the point: a
change of row arrangement changes which candidates come out, hence every later batch, so the
whole-computation effect and the per-elimination effect are different measurements.

`elimination_density` reports the density a representation policy would have to read: the
distribution of row densities as built and at each row's own peak during its reduction, the density
of the densest 64x64 blocks, and the three backends' elimination times with representation
conversion in its own column. A global density of a fraction of a percent says nothing about
either. A last table divides each backend's time by the `row_operations` it reported, which is the
per-operation cost a change inside a row operation has to move, and states the pivot index's
storage at the instance's widest matrix. `-- list` names the instances; the largest are excluded by
default, because a dense representation of katsura-7 grevlex is 374 MB for a matrix holding 112k
entries.

`accumulator_span` answers whether the shipped elimination backend has a loop a SIMD kernel could
go in. `Backend::Adaptive`'s inner operation walks the *pivot's* sparse entries and indexes a dense
buffer, which is a gather and a scatter; the only contiguous alternative updates the pivot's whole
span `[leading_column, trailing_column]`, and `span / support` is the extra cell updates that would
cost. The harness reports that multiplier weighted by row operations, the share of row operations
whose span is too short to fill a vector, the occupancy of the pivot within its span by decile, and
an accounting of all three of the accumulator's loops so the two that are *already* contiguous can
be sized. Everything is reported for **both reduction strategies**, which matters more than it
sounds: the two do not see the same matrices, and the multiplier is 4.04x under the baseline
against **9.81x** under the one `F4Options::default()` runs. It is a property of the matrices rather
than a timing, so it reproduces exactly and needs no exclusive lock — and it is self-checking: for
every matrix it also runs the real backend, split form included, and asserts its replay applied the
same pivots, by `row_operations` and `pivot_inversions`. The answer, measured, is **no** — see
[`docs/MILESTONE-SIMD-PARALLELISM.md`](../MILESTONE-SIMD-PARALLELISM.md) §10.

`boolean_density` answers what a `GF(2)` coefficient costs to store, which is #218's last open
question. A sparse entry is `(usize, F)` and the index's alignment pads it to **16 bytes at any
field width**, so over `GF(2)` it is 16 bytes carrying one bit — a factor of 128, and a
representation cost rather than an arithmetic one. The harness eliminates the *same* structural
system at two field widths — random quadratics with `x_i^2 - x_i` adjoined, which over `GF(2)` are
the field equations and are asserted to be — and reports entries, peak live entries, row operations
and per-backend times for each. The counts are exact and reproduce bit-for-bit; the measured
surprise is that `GF(2)` needs about **half** the entries and half the row operations of the wide
field on the same system, because `a + a = 0` makes cancellation far more frequent. So `GF(2)` is
already cheaper in memory — by entry count, not entry size. It also runs all three elimination
backends over characteristic-two matrices and asserts they agree, which
[`docs/research/boolean-solving.md`](../research/boolean-solving.md) §15 explains had never been
checked.

`f4_selection` compares every reducer-selection policy and the cache against one common baseline,
on one line each: the closure size, the largest matrix, the peak live entries, the row operations,
the share of reducer multiples that had been needed before, and the stage times. The policies come
from `ReducerSelection::ALL`, so one added to the enum is measured without the program being
edited, and every row's basis is asserted equal to the first row's.
`f4_profile`'s configurations bundle several options together, so neither effect can be attributed
from it alone.

`f4_ablation` runs twelve configurations over the corpus and asserts every one returns the
baseline's basis, which is what establishes that the optimizations compose rather than conflict.
`f4_milestone` is the headline comparison: both engines on identical inputs in one process, with
the bases asserted equal wherever both can run. It reports **two** ratios, because the pair
criteria are shared machinery and the two functions' defaults do not match — see "Choosing a
strategy" below. `buchberger_reach` runs the classical engine on one hard instance per invocation
so an external timeout can bound it, which is how a dash in that table is shown to mean "does not
finish" rather than "was not tried".

`fglm_baseline` classifies each benchmark system as unit, zero-dimensional, or
positive-dimensional from the leading monomials of its grevlex basis, reports the dimension `D` of
`R/I` as a vector space, and times a lex basis against a grevlex one under both engines. It is the
baseline for the order-conversion work; **cyclic-4 is positive-dimensional**, so FGLM does not
apply to it, and that is measured rather than assumed.

`fglm_profile` attributes a conversion's cost. One table is the shape of the border — how many of
the `N * D` operator columns leave the standard monomials, and how many *distinct* monomials those
are, whose gap bounds what deduplicating them could remove. The other is the stage breakdown
(standard-monomial enumeration, border classification, scalar normal forms, a batch's symbolic
closure, coordinate assembly, the lex walk) beside what the representations hold. Scalar reduction
and batched reduction are the same stage under two strategies, so one column is zero whenever the
other is not and the reported share is of their sum. It profiles the shipped strategies, or M17's
with `-- baseline`. It sets `FglmOptions::measure_stages`, which is off by
default because the operator loop runs `N * D` times and a clock read inside it is not free. The
byte figures are estimates of this crate's own representations;
`zeebra::util::peak_resident_bytes` is the separate, process-wide measurement, and the two are not
interchangeable.

`fglm_border` prices the three `OperatorConstruction` strategies against each other on the same
prepared source basis, having first asserted that they build identical operators, and varies the
batch size — which is the trade that decides the recommended default rather than being left to a
guess. It also answers,
with its own measurement rather than by inference, whether the one-term polynomial built per border
reduction is worth avoiding: 0.07% to 0.38% of the reduction it precedes on the families where
reduction dominates, so no. `cargo bench --bench fglm -- fglm_operator_construction` is the same
comparison under Criterion.

`fglm_parallel` is why the batched border reduction is **not** parallelized, measured rather than
argued, and it is the entry point for anyone who wants to re-open that. Its target loop is the one
loop in the project whose iterations are genuinely independent — the reducer pivots are fixed before
any border monomial is touched — and that is not enough. Four tables, selected by name because they
want different machine conditions: `per-batch` splits a batch's clock between the symbolic closure
and the target loop (two single-threaded tables, one pinned core); `floor` prices one
`std::thread::scope` dispatch on this machine; `carry` prices the `dirty_from` carry a split gives
up, sequentially, so it is separated from the dispatch cost; and `sweep` runs the reduction on up to
128 scoped threads with every row's remainders asserted bit-identical to the one-worker row's. At
the recommended batch of 64 a batch's target loop is 8 to 210 µs against 21 µs per worker, so one
worker is the fastest row on every system in the corpus. §6.8 of
[`docs/MILESTONE-FGLM-SCALABILITY.md`](../MILESTONE-FGLM-SCALABILITY.md) has the figures and the
decision; `BorderReduction::Grouped` is the decomposition without the threads, kept because the
carry's cost is a measurement.

`wiedemann_conversion` alternates classical and adaptive conversion on identical prepared bases,
asserts exact basis equality, and prints the chosen route, projection attempts, fallback reason,
operator-construction time, dependence time and output digest. Its process peak spans all repeats;
use separate `--route classical` and `--route adaptive` processes for per-route memory.
`--msolve PATH` checks the eliminant through the existing bounded adapter. See the
[conversion guide](grobner-bases.md#certified-scalar-wiedemann) for input format and limits.

`fglm_shape` is M18-4's dense research spike, measured. `grobner::fglm::shape` detects **shape
position** — whether a single variable's powers `1, t, ..., t^{D-1}` are a basis of `R/I` — and
where the last variable qualifies it produces the lex basis `p(t), x_0 - h_0(t), ...` from that
variable's Krylov sequence, with no monomial walk and without retaining the accepted quotient
vectors. The whole katsura family qualifies and nothing else in the corpus does; 76 of 120
zero-dimensional differential fixtures do, and the route is checked against Singular on every one.

Detection is **algebraic, not a count of solutions**: `<x - 1, (y - 1)^2>` has one point, dimension
two, and is in shape position, while `<x^2, y^2>` has one point, dimension four, and is not. The
output is verified before it is returned — every polynomial's class in `R/I` must be zero, which
with the leading monomials proves it is the reduced lex basis — so nothing probabilistic is
exposed. It is public and tested but not a `FglmOptions` strategy; `docs/MILESTONE-FGLM-SCALABILITY.md`
§8.5 is the **no-go** on a full sparse-FGLM milestone and the measurements behind it.
[`docs/research/wiedemann-krylov.md`](../research/wiedemann-krylov.md) is the decision record for
Wiedemann and Krylov methods in both places this crate eliminates — **won't-do** for F4's
echelonization, and a deferral for order conversion that M25's competitive baseline has since
reopened as staged work. Read it before proposing either.
[`docs/research/order-conversion.md`](../research/order-conversion.md) is the survey of what else
there is: eight alternatives to the classical conversion, each with a verdict and the measured figure
that settles it, and the reaffirmed-but-narrowed §8.5 no-go. Its §4 records shape position measured on a cipher-derived family — machine-independent,
because a minimal-polynomial degree is not a timing.

`grobner::shape_position_hypotheses` is the cheap syntactic half of the same question, from Campa and
Roy's Theorem 8 (eprint 2025/814): zero-dimensionality, a pure-power leader for every variable, and a
finite `deg_≺`-top-form quotient, each decided from the basis for the price of a Hilbert series
rather than a quotient algebra. It is **not** called a certificate of shape position, because those
hypotheses do not imply it — `test_the_published_hypotheses_are_not_sufficient` exhibits an ideal
that discharges every one of them and is not in shape position. The full reading, including the
hypothesis Theorem 8's proof invokes and its statement omits, is in `docs/research/anemoi.md`
§10.5, which moved out with the cryptanalysis research in #668 and is preserved at commit
`9532a9a2`. The missing condition is exactly
`shape_report`'s `minimal_polynomial_degree == dimension`, so the two together are what settles a
family and the module's docs say which half is a deduction and which a computation.

`fglm_storage` reports the operator representations three ways: bytes under each strategy, which are
exact; operator *application*, on a unit input and a dense one, because the sparse path skips a zero
input coordinate and the dense path does not; and the whole conversion, where the difference turns
out to be under 1%. `cargo bench --bench fglm -- fglm_operator_application` is the application half
under Criterion.

`fglm_ablation` runs every construction × storage combination on one source basis per system, with
the lex basis and the operators' nonzero count asserted equal to the baseline's on every row, and
reports time and memory side by side. **It is where the defaults came from.** The shipped
configuration is at least as fast as M17's on every system in the corpus — 14.0x on katsura-7, 1.17x
on planted-10 — and never stores more. Two changes cannot be ablated and the example says so: the
compact sparse column and the span's two triangular blocks are not strategies, so they are in every
row including the baseline. `cargo bench --bench fglm -- fglm_recommended` is the same comparison
under Criterion, and `fglm_profile` shows what that left behind: border reduction was 95% of
katsura-7's conversion and is 52%, while planted-10's lex walk is the majority of its own —
M18 did not touch it, and two follow-ups did: offsetting each echelon row's coordinates by its
pivot, and reducing into registers the span owns rather than allocating a residue per candidate.
Together, on one pinned and interleaved protocol, they take planted-10's lex walk from 23.2 ms to
11.1 ms — 2.09x — and the conversion's dense blocks from 20,484 kB to 16,392 kB, which is a fifth
of them and not a quarter.

Recorded baselines, before/after measurements, and the reasoning behind each optimization are in
[`docs/MILESTONE-ALGEBRA-FOUNDATION.md`](../MILESTONE-ALGEBRA-FOUNDATION.md),
[`docs/MILESTONE-F4.md`](../MILESTONE-F4.md),
[`docs/MILESTONE-F4-OPTIMIZATION.md`](../MILESTONE-F4-OPTIMIZATION.md),
[`docs/MILESTONE-FGLM-SOLVING.md`](../MILESTONE-FGLM-SOLVING.md),
[`docs/MILESTONE-FGLM-SCALABILITY.md`](../MILESTONE-FGLM-SCALABILITY.md),
[`docs/MILESTONE-SIMD-PARALLELISM.md`](../MILESTONE-SIMD-PARALLELISM.md),
[`docs/MILESTONE-LARGE-PRIME-FIELDS.md`](../MILESTONE-LARGE-PRIME-FIELDS.md),
[`docs/MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md`](../MILESTONE-RESOURCE-AWARE-CRYPTANALYSIS.md),
[`docs/MILESTONE-DEGREE-AWARE-F4.md`](../MILESTONE-DEGREE-AWARE-F4.md),
and
[`docs/MILESTONE-COMPETITIVE-ALGEBRA.md`](../MILESTONE-COMPETITIVE-ALGEBRA.md).
[`docs/MILESTONE-ALGORITHMIC-ELIMINATION.md`](../MILESTONE-ALGORITHMIC-ELIMINATION.md) is the
current plan rather than a record of measurements taken, and
[`docs/MILESTONE-COMPETITIVE-MQ-SOLVING.md`](../MILESTONE-COMPETITIVE-MQ-SOLVING.md) is the next
one. That plan opens by recording that the one before it is unfinished, because its own scope
depends on measurements M26 has not yet reported.

M25 calibrated Zeebra against external solvers on identical problems; where a published conversion wall was checked it **did not reproduce**: 46 s here against 6.13 h reported, and a within-run conversion/basis ratio of 1.71 against 2 367.

That milestone's §10.1 is worth reading on its own. It scores the plan's own predictions and finds
that every one about a stage already measured held, while three of four about quantities nobody had
measured were wrong by more than an order of magnitude — one by 838x.

### Sylvester kernel comparison

`determinant_width --compare-kernels` times dense and Euclidean kernels in alternating order,
asserts identical sample vectors on every draw, and prints each draw plus the ratio of the two
medians. `--width` is repeatable; `--samples` is rounded up to a multiple of each width so every
requested worker receives work. Both kernels use the same fixed-seed pair and consecutive sample
points. `--pair synthetic` (default) has degree one in the surviving variable; `--pair triangular`
includes quadratic specialization work. Neither is a registered cryptanalytic instance.

Build before taking the benchmark lock, then pin to 32 physical cores (verify the topology on
your machine). On the development workstation:

```sh
cargo build --release --example determinant_width
ZEEBRA_MACHINE=5995wx ZEEBRA_AFFINITY=0-31 \
  tools/benchlock.sh sylvester-297 timeout 600 taskset --cpu-list 0-31 \
  target/release/examples/determinant_width --compare-kernels \
  --order 1458 --width 32 --samples 128 --repeats 3
```

If you set `CARGO_TARGET_DIR`, replace `target/release` with that directory's `release` path.
Use `--order 162 --samples 32 --repeats 1` for a quick check. `--compare-kernels` cannot be combined
with `--kernel` or `--count-allocations`; order must be positive and even. Initial load above eight
refuses the run. Retain all draws and examine their spread and the benchmark-lock load log before
publishing; a short Euclidean batch can be dominated by thread creation. The ratio includes sample
specialization and thread creation but excludes coefficient extraction, interpolation, root finding
and verification. It is a kernel-stage comparison and cannot be quoted as a solver speedup.

### Monomial order width

Build before acquiring the benchmark lock. Choose a CPU in the current affinity mask and check
the machine load and runnable count while holding the lock.

```sh
env -u RUSTFLAGS RUSTC_WRAPPER="" CARGO_TARGET_DIR=target-width \
  cargo build --release --example monomial_order_width
tools/benchlock.sh monomial-order-width bash -c \
  'cat /proc/loadavg && taskset --cpu-list 2 target-width/release/examples/monomial_order_width'
```

The harness compares production with four-variant and three-variant versions of the same built-in
comparators. It times forced per-comparison dispatch and replays the unstable sort over recommended
F4 column snapshots. It checks the dispatch checksums and sorted columns across arms.
Run `cargo test --example monomial_order_width` for the fixed checksum and layout check that also
runs in CI. See the [measurement and scope](../research/monomial-order-width.md).
