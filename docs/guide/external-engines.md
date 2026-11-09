# External engines: differential testing and comparison

Differential testing against Singular, and the contract for driving Singular, msolve, Groebner.jl
and Sagebrush as comparands.

## Differential testing against Singular

`zeebra-differential` generates deterministic polynomial systems, asks a local Singular about each
one, and compares **every intermediate result** — not only the lex basis:

```sh
cargo run --release --bin zeebra-differential -- --help
cargo run --release --bin zeebra-differential -- --systems 500
cargo run --release --bin zeebra-differential -- --systems 500 --jobs 8   # eight at a time
cargo run --release --bin zeebra-differential -- --seed 777 --systems 240 \
    --max-degree 4 --max-terms 5 \
    --fixtures src/grobner/differential/fixtures.rs   # regenerate the committed cases
cargo run --release --bin zeebra-differential -- --fields 2^8/283 --seed 3780 --systems 40 \
    --max-degree 4 --max-terms 5 --fixture-table FIXTURES_GF256 \
    --fixtures src/grobner/differential/fixtures_gf256.rs   # the AES-modulus GF(2^8) table
cargo run --release --bin zeebra-differential -- --fields 2^8/285 --seed 4210 --systems 40 \
    --max-degree 4 --max-terms 5 --timeout 300 --fixture-table FIXTURES_GF256MQ \
    --fixtures src/grobner/differential/fixtures_gf256mq.rs   # the Fukuoka-modulus table
```

**Three committed tables, over eight fields.** The split is per sweep rather than per field: a
generated header's regeneration command is only true of the sweep that wrote it, so adding a field
to an existing sweep's `--fields` list would change which field every later seed is generated over
and replace every answer already recorded. The two GF(2^8) tables are the two *moduli* — `0x11B`,
which HFE is posed over, and `0x11D`, which the **Fukuoka MQ Challenge** is posed over — and they
are not two samples of one field: `test_both_degree_eight_binary_fields_are_supported_and_distinct`
asserts the moduli differ *and* that `0x57 * 0x83` differs under them, so a harness sweeping one
field twice fails rather than looking like coverage. Each table is checkable only against its own
modulus, which
`test_a_gf256mq_case_checked_modulo_the_other_polynomial_is_rejected` pins in both directions.

`--timeout` appears in the third header because it had to: at the default 30 s one five-variable
system in that seed's range outruns Singular and the sweep records 39 fixtures instead of 40, so a
header omitting it would not reproduce its own table. It is the one flag echoed into a header that
does not change *which* systems are generated — only which of them get an answer.

**`--fields` names a field and not a characteristic**, because a characteristic does not determine
one: `GF(2)` and `GF(2^8)` share it, and `2^8/283` and `2^8/285` are two fields of the same order in
which the same byte has two different squares — `Gf256` and `Gf256Mq`. A case records its modulus,
and the modulus is *asserted* to agree on both sides rather than assumed: Zeebra's end by
multiplying (`x^m = r` determines `P = x^m + r`, so one exponentiation accepts exactly one modulus),
and Singular's by declaring `ring R = (2,a),...` with an explicit `minpoly` — its own `(2^8,a)`
Galois fields take theirs from an internal table a script cannot choose — and comparing the echo.
A ring reducing by something else is an oracle failure and never a comparison. `--characteristics`
is still accepted as the old name, so the committed tables' regeneration commands keep running.

**`--jobs` does not change the answer.** Each system is a Gröbner basis, an FGLM conversion and a
blocking Singular subprocess, and `system(index)` is a pure function of `(seed, index)` — nothing
in a system's check reads another's result, so the sweep fans out over whole systems. Each worker
gets its own `SingularOracle` with its own `worker-<i>` scratch subdirectory, because a run's
scratch files are named from a per-oracle counter and two workers in one directory would overwrite
each other's script. The report is assembled **in index order and not in completion order**, and
the progress callback is held back to index order too: a seeded sweep whose failure list depended
on which worker finished first could not be reproduced. `--jobs 1` is the sequential sweep, which
is the default, and the report is pinned equal across one, four and eight jobs by
`test_a_concurrent_sweep_reproduces_the_sequential_report`. `--jobs` is deliberately *not* recorded
in a generated fixture module's regeneration command, since it cannot change a recorded answer.

The comparison runs outwards from the source basis and stops at the first disagreement, so what it
reports is the earliest thing that differs rather than everything downstream of it:

| check | Zeebra | Singular |
|---|---|---|
| source basis | `f4` under grevlex | `std` in a `dp` ring |
| quotient dimension | `QuotientBasis` | `vdim` |
| standard monomials | `QuotientBasis::monomials` | `kbase` |
| border normal forms | `normal_form` of each `u` in `∂B` | `reduce(u, G)` |
| operator columns | each column of each `T_i` | the normal form of the monomial it stands for |
| lex basis | `fglm_to_lex` | `std` in an `lp` ring, cross-checked against Singular's own `fglm` |

**Multiplication-operator columns are compared individually.** Each has a precise mathematical
answer, so a wrong column is caught directly rather than only when it happens to change the lex
basis. On two 1,000-system sweeps under the shipped defaults, over GF(2), GF(3), GF(7), GF(13),
GF(65537) and GF(2^31 - 1) in two to five variables, every system agreed: 949 zero-dimensional, 572
unit ideals, and 479 positive-dimensional ideals that both sides rejected, with no oracle
failures.

**An oracle that did not answer is never agreement.** Singular exits 0 after a script error, so a
successful exit proves nothing: every run must reach an end-of-script marker *and* have printed no
error line, and a timeout, a missing binary, a characteristic above Singular's `2^31` limit, or an
answer Singular's own `fglm` contradicts each make the sweep exit non-zero.

A failing case is written out as a fixture literal, shrunk first — generators dropped, terms
dropped, coefficients flattened, exponents lowered — while it keeps failing *the same* check. The
original system and its seed are kept beside the shrunk one, since a shrunk system is no longer
what the seed generates.

**CI needs no Singular.** A sweep's agreeing cases are emitted as Rust literals into
`src/grobner/differential/fixtures.rs`, and an ordinary test replays the same comparison against
them — a table of constants where the subprocess was. A separate test corrupts a fixture six ways
and requires each to be detected, so a passing table is evidence rather than an absence of
checking. The live sweep is also available as an `#[ignore]`d test:

```sh
cargo test --release --lib -- --ignored --exact \
    grobner::differential::tests::test_a_live_sweep_against_singular_agrees
```

One more needs data this repository does not redistribute. The Fukuoka MQ Challenge files are
"All Rights Reserved" with no stated licence, so the test against a genuine instance is opt-in for
the same reason:

```sh
tools/fetch-mq-challenge.sh
cargo test --release --lib -- --ignored --exact \
    grobner::research::mq::tests::test_a_published_instance_is_reproduced
cargo test --release --lib -- --ignored --exact \
    grobner::research::mq::tests::test_the_real_n24_challenges_import
# the three #197 added: the modulus oracle, the GF(2) families, and the two real m = 16 instances
# checked against the answer vectors their 2015 solver published
cargo test --release --lib -- --ignored --exact \
    grobner::research::mq::tests::test_the_published_answer_vanishes_only_under_the_challenges_modulus
cargo test --release --lib -- --ignored --exact \
    grobner::research::mq::tests::test_the_published_gf2_instances_import
cargo test --release --lib -- --ignored --exact \
    grobner::research::mq::tests::test_the_real_m16_challenges_vanish_at_their_published_answers
```

## Other external engines, for comparison

Singular is the oracle above because it is the one this repository has always had installed.
Three more comparands — **msolve**, **Groebner.jl** and **Sagebrush** — are provisioned into a
user prefix by one script, with pinned versions and no root:

```sh
tools/external/provision.sh          # ~5 min cold, 0.2 s warm; no root needed
. tools/external/env.sh              # PATH, LD_LIBRARY_PATH, JULIA_DEPOT_PATH
tools/external/smoke/smoke.sh        # all four on one system; non-zero exit on disagreement
```

**The roster stops there, and Magma is the reason to say so** (#430). Magma is the fastest engine in
every column of the published comparisons and it cannot be provisioned: it is commercial and there
is no licence here, so every Magma figure in this repository is read from a page or a paper and
quoted, never measured — `docs/research/classical-benchmarks.md` §2.3 is the current one, V2.27 on an
i7-7700. Macaulay 2 is free and provisionable and is deliberately not provisioned, being a
Buchberger-era engine that would measure little.

Nothing is linked and nothing is vendored: every one of them is run as a **separate process**,
which is what makes a GPL engine usable from an MIT crate at all. The rules are
`docs/research/external-provenance-policy.md`; what got installed, how to invoke each tool for a
basis, for an eliminant and for solutions, what each one means by "degrevlex", the prime-field
ceilings (msolve and Singular both stop at 2^31 − 1), and the smoke-test agreement are in
`docs/research/external-comparands.md`.

Each engine is driven through one trait, `grobner::external::ExternalSolver`, behind the
`external-runners` feature — on by default, and adding no dependency, because the interface to
every one of these tools is text. **Zeebra goes through the same trait**, so the in-crate row
cannot acquire a privilege the subprocess rows lack — including the refusals: `ZeebraSolver` serves
the basis, lex-basis, conversion and univariate-eliminant tasks and refuses the two solution tasks
(no comparand offers either) and the cryptanalytic witness (it belongs to the other scoreboard).
The eliminant is served as the *projection* it is — `I ∩ k[x_n]` is generated by the one element of
a reduced lex basis involving no other variable — so it adds no algorithm; it was previously refused
alongside the solution tasks under a reason that was true for them and false for it, which left the
one task with two external engines and no in-crate operand (#465). Note the field that comparison
lives at: msolve's eliminant bound is below 2^31 − 1, so it is the corpus's `2^30 + 3` and not the
reference prime, and `ZeebraSolver` compiles the ladder's dimensions at both for that reason.
`msolve::tests::test_a_real_msolve_and_zeebra_return_the_same_eliminant` compares the two
engines' eliminants as **polynomials** rather than as text.

`SingularSolver` is the reference adapter and `MsolveSolver` the one with the most to say:

```rust
use std::time::Duration;
use zeebra::grobner::external::{ExternalSolver, FieldSpec, Instance, Limits, MsolveSolver, Task};
use zeebra::MonomialOrder;

let mut solver = MsolveSolver::new("msolve", std::env::temp_dir().join("zb-msolve-doc"));
let instance = Instance::new(
    "pair",
    "doc",
    FieldSpec::prime(1073741827),
    vec!["x".to_string(), "y".to_string()],
    vec!["x^2-2".to_string(), "y-x-1".to_string()],
    MonomialOrder::GradedReverseLexicographic,
);

// Capability is answered without running anything, and a `no` is never a timing.
assert!(solver.supports(&instance, Task::ReducedGrobnerBasis).is_supported());
// msolve has no lex order at all, so a lex basis is a capability gap rather than a slow row.
assert!(!solver.supports(&instance, Task::LexBasis).is_supported());

// An absent binary is reported, never fatal — so a sweep continues past it.
let report = solver.run(&instance, Task::ReducedGrobnerBasis, &Limits::wall(Duration::from_secs(30)));
assert!(report.status.answered() || report.was_skipped());
```

An absent binary is resolved by `process::unavailable_binary`, a path lookup that starts nothing,
**before** the run writes its input file and before the supervisor's clock starts — so the
"unavailable" verdict never competes with the wall budget the run was given and the row is skipped
under any budget, including none. Only definite absence takes that short cut; a file that exists
but may not be executable is left to the spawn, whose reason is the kernel's rather than a guess.

`RunReport::was_skipped()` is true for the four outcomes that mean **the tool did not run**:
`Unsupported` (the input is unrepresentable), `RunFailure::Unavailable` (the tool is absent),
`RunFailure::Environment` (the harness's own environment would have invalidated the measurement)
and `RunFailure::Harness` (the harness's own filesystem work failed).
`Environment` is why it exists: an adapter can set a child's environment but cannot *clear* it, so an
inherited switch that selects a different algorithm — or writes a trace into the stream the basis
is parsed from — cannot be undone from inside the run, and the honest answer is to refuse rather
than to measure something no user of the tool gets. It is deliberately not `Reported`, which means
"the tool printed an error"; there was no execution to print one. The variant names the variable so
an operator knows what to unset and the effect so the refusal can be judged. Sagebrush has seven
such switches (`sagebrush::PINNED_SWITCHES`), every one read with `env::var(..).is_ok()` — truthy
if set, so `SB_SIGF4=0` *enables* the experimental signature path.

`RunFailure::Harness` is the same argument applied to the filesystem, and the two I/O variants are
split by **which side failed**. Every adapter writes its own scratch files — the input or the
script, and through `Supervisor` the work directory and the output the child's streams are
redirected to. A failed write there is the harness's, the tool was never started, and a full disk
or an exhausted fd table says nothing about msolve. `RunFailure::Io` is the other side: I/O the
tool itself reported, such as msolve's `Cannot open output file`, which is an attempted run and so
is **not** skipped. `From<std::io::Error>` lands on `Harness` because an adapter only ever sees a
`std::io::Error` from work it did itself; the tool's own complaints arrive as text in a log and are
classified by reading it. `SpawnError::Harness` and `OracleError::Harness` are the same
distinction one layer down — the supervisor and the Singular oracle never speak for the tool.

Two msolve-specific facts the adapter encodes as named constants, because both are capability
bounds rather than slow paths and both are narrower than they look:

* `msolve::MAX_CHARACTERISTIC` is `2^31` — a basis works for any `p` below it.
* `msolve::MAX_CHARACTERISTIC_ELIMINANT` is `1515531529`. msolve's sparse-FGLM refuses primes at
  or above `1518500213` and its genericity handler then retries **without bound** rather than
  failing, so the eliminant task is refused instead of being allowed to burn a wall limit; the
  constant is the tighter *documented-safe* accumulation bound rather than msolve's own guard,
  because primes between the two run with no accumulation guarantee. `Mersenne31` and
  `Zp2147483647` are both above it.

msolve also has **three** failure modes that exit 0. On a staircase that is not generic enough it
permutes the variables and appends a new one carrying a random linear form, then writes a
well-formed parametrization of the ideal it substituted — so the adapter compares the output's
variable list against the instance's on every run. Its sparse-FGLM refuses a too-large prime and
then retries forever rather than failing. And a generator naming a variable that is not on line 1
has that factor **silently dropped**, so `supports()` checks every identifier in every generator
against the declared order before anything runs.

That last one is also why msolve is safe at ten or more variables, where `x1` is a prefix of `x10`:
it matches factor names with a full `strcmp` rather than greedily, verified by handing it 53
distinct degree-2 monomials over `x1..x14` and getting the same set back. Cross-engine agreement
cannot catch a tokenizer bug — every engine is handed the same bytes, so all of them agree on the
same wrong ideal — which is why that check is against the input rather than against another tool.

All three, the mapping from msolve's F4 stage names onto Zeebra's, and what of its design is worth
reimplementing are in `docs/research/msolve-implementation.md`.

The msolve adapter's corpus agreement test builds **Zeebra's side by parsing the rung's own text**
and dispatching on **variable count**, so a corpus family added at a width already present — 4, 5,
6, 7, 10 or 14 — gets an oracle with no edit. It is also the stronger check: the bytes parsed are
the bytes every engine is handed, so a round-trip failure in either direction shows up as a
disagreement rather than as a silently different problem. Every rung is at the reference field,
so every rung has one; a rung added at another field would need a second field *type* rather than a
second match arm.

The ladder is the public benchmark set: Katsura, Cyclic, random MQ and planted MQ. A caller
benchmarking systems of its own builds `CorpusEntry` values for them — each with its recorded
`Equivalence` — and passes them to `CompetitiveBoard::with_corpus`, which applies the same
publication gates to those rows as to the ladder's. The Zeebra adapter also compiles KoalaBear
(`corpus::KOALABEAR_CHARACTERISTIC`) and `2^64 - 353` (`corpus::WIDE_64_CHARACTERISTIC`) at a few
widths, for systems that are not on the ladder.

That test is not `#[ignore]`d — it runs whenever msolve is installed — so by default it builds
oracles only up to seven variables, which is 1.4 s for nine rungs where `mq-random-10` alone did
not finish in ten minutes. **`ZEEBRA_FULL_CORPUS_ORACLE=1` lifts that ceiling** for a machine that
wants the ten- and fourteen-variable rungs covered. Rungs left out are printed with the remedy,
never silently dropped. (`F4Options::max_wall_time` does not substitute for the ceiling: it is
checked once per batch, so one long matrix reduction overruns it.)

`GroebnerJlSolver` and `SagebrushSolver` are built the same way, and both read what
`tools/external/env.sh` exports: `GroebnerJlSolver::from_env(work_dir)` and
`SagebrushSolver::from_env(work_dir)`. Two things about them are worth knowing before reading
a figure from either.

**Groebner.jl's process wall time is a measurement of the Julia compiler.** On the smoke system it
is 5.47 s against an inner `groebner` call of 0.18 ms. The adapter therefore warms the JIT on a
proxy system in the same ring and reports the *timed call* as the run's wall time, keeping the
process wall and CPU as stages so nothing is excluded without being recorded; the measured residue
after the warm-up is about 0.17 ms, an absolute constant rather than a factor. It is the one
adapter in the module where `wall` is not the process's, and
`src/grobner/external/groebner_jl.rs` says so at the top.

**Sagebrush is the only permissively licensed comparand, and the only one with no release.** It is
five weeks old, every engine crate is `0.1.0`, its `f4.rs` carries six tests, and no committed
oracle run in its own repository exercises the elimination. It also agrees with Zeebra **term for
term, every coefficient included** on every Katsura and Cyclic rung of the shared corpus, plus the
reference smoke system, a 62-bit prime and a fourteen-variable system — ten instances — and across
the full ladder — eighteen rungs then, twenty-six since #424 — it has **disagreed with nothing**. Both halves belong in any table that
quotes it: report its rows with the pinned SHA, and do not make it the denominator of a headline
speedup. The verdict is `docs/research/sagebrush-implementation.md` §6.3.

**It is also the only comparand that offers both routes to a lex basis.** The driver takes
`--order lex|deglex|degrevlex` and `--route f4|fglm`, so `SagebrushSolver` covers
`ReducedGrobnerBasis` under any of Zeebra's three orders, `LexBasis` by the engine's direct lex F4,
and `LexBasisByConversion` by `fglm::groebner_fglm` — which gives that last task a second comparand
beside Singular, Groebner.jl 0.10.11 having no FGLM at all. The two routes are deliberately
separate tasks: they return the same basis by different algorithms, so a column that mixed them
would compare two complexities under one heading, and the adapter checks the driver's echoed
`#route:` line on every run for exactly that reason. FGLM carries its **own** field ceiling of
`2^31`, an eighth of the basis route's `2^62`, and the adapter declares it per task rather than
letting a sweep discover it as a wall-clock stop.

Neither tool confuses `x1` with `x10`, which matters because the corpus has fourteen-variable
rungs and **cross-engine agreement cannot catch a tokenizer bug** — every engine is handed the same
bytes, so all of them would agree on the same wrong ideal. **Both adapters now check their echoed
generators against the sent system on every run**, comparing canonical term multisets so that
`x1*x10-1` and `1*x1*x10 + 1073741826` count as the same polynomial, and reporting a mismatch as
`RunFailure::SelfInconsistent`. So a `Complete` status on a fourteen-variable rung is itself the
proof, for Groebner.jl's `@gen` echo and for the Sagebrush driver's `#gen` echo alike. The
behavioural test remains, because it checks the *consequence* in the computed basis and would still
fail if a parser read the system correctly and then packed it wrongly.

Because the Sagebrush driver lives in the provisioning prefix rather than in this repository, it
prints a `#driver contract:` version that the adapter **requires**: an adapter that checked the echo
only when it happened to be present would silently stop checking against an older installed binary,
which is worse than not checking at all. A driver predating the marker fails with
`RunFailure::Incomplete` naming `tools/external/provision.sh`, so the remedy is in the error.

**That same prefix is a third way to lose the ISA floor, and it had lost it.** The driver is built
by `cd`-ing into the prefix, so cargo resolved config from there upward and the comparand was
compiled at baseline `x86-64` with no LTO while Zeebra's side of every comparison ran at
`x86-64-v3` under fat LTO at one codegen unit (#385) — "a comparison between a tool built for its
distribution's baseline and one built for the host is not a comparison of algorithms", as
`docs/research/external-comparison-protocol.md` puts it. For a comparand this repository builds
from source, the fix is to **match the floor** rather than record the gap, and raising it makes the
*comparand* faster, so it is not a self-serving change. `provision.sh` now passes
`-C target-cpu=x86-64-v3` (overridable with `ZEEBRA_EXT_DRIVER_TARGET_CPU`) and the driver's own
`Cargo.toml` restates `lto = "fat"` and `codegen-units = 1`.

The part that makes it checkable is that **the comparand reports its own floor**: the driver prints
`#isa floor:` from a compile-time `cfg!(target_feature = ..)` — the only sound instrument, since a
census of the artifact cannot separate a raised floor from an explicitly dispatched
`#[target_feature]` kernel — and the adapter records it in the row's `ToolVersion` as
`<pinned sha>, built for x86-64-v3 or better (AVX2)`. The marker arrived with contract 3, so an
older installed driver is refused rather than measured against a configuration it was not built
with. The board's existing Sagebrush rows predate the change, say so through their own build
identity, and are re-taken by #520.

The agreement checks are live tests, `#[ignore]`d because CI has neither tool installed and a test
that silently passed when the tool is absent would be worse than no test:

```sh
. tools/external/env.sh
cargo test --release --test external_comparands -- --ignored --test-threads 1
```

What is inside each engine — Groebner.jl's monomial encodings, hashtable and learn/apply traces,
and which of those are msolve's rather than its own; Sagebrush's F4, its 2^62 modulus ceiling, and
what reusing any of it would require — is in `docs/research/groebner-jl-implementation.md` and
`docs/research/sagebrush-implementation.md`.

`tools/external/groebner-jl-counts.jl` takes the other side of the comparison: it reads the
canonical text of a digest-pinned instance (`f4_profile -- mq-instance`), rebuilds it in the same
ring and ordering the adapter uses, and reports **Groebner.jl's own** pair, matrix and row counters
plus its per-stage split — the latter by enabling the package's own `TimerOutputs` timer at runtime,
which needs no patched build. It is a measurement instrument on no build path, and
`docs/research/groebner-jl-gap.md` is what it produced: the 348x on `mq-random-10` decomposed into
randomized linear algebra (4.89x, declined by policy), interreduction done by division rather than
by one Macaulay matrix (5.03x), and a per-operation representation constant (14.0x).

[`docs/research/m27-baseline.md`](../research/m27-baseline.md) is the frozen baseline these
ratios are quoted against: which cohort each engine's rows belong to, the cryptanalysis frontier by
class, the `poseidon31-cico-t16-rf4-rp2` row resolved across its three cost tables, and the rule for
when a ratio carries the #318/#319 systematic. **Cite it rather than re-deriving a baseline.** Three
things it establishes that are easy to get wrong: a ratio formed *within* one cohort carries no
systematic while one spanning a pre-M25 record carries +26%/−8%; `mq-random-10`'s interreduction
share was unchanged at ~80% after #437 and stayed ~80% on the default path for as long as
`F4Options::recommended()` selected the division route — **#575 moved that**, so the ~80% figure now
describes `baseline()` and not the shipping path; and the interreduction A/B measures **3.63x** end
to end on a box whose division side matches the board row, against the 4.18x measured on one 1.40x
slower than it.

#507 then took that A/B as a **five-engine board cohort** rather than a projection, and
[`docs/research/interreduction-cost.md`](../research/interreduction-cost.md) §3e is the result:
**8 333.1 ms** measured against 7 999 ms projected, **1.07x behind Singular** on
`reduced-grobner-basis` and **parity on `lex-basis-by-conversion`** (1.09x ahead, inside the box's
spread), with the matrix route ahead on
every graded rung of the ladder above the timer's noise floor (1.01x–3.78x) and behind on every lex
one (up to 6.25x, because a shape-position lex basis makes katsura-6 build 7 983 × 8 015 for a
six-element basis). #507 left the default on the division route, because `katsura-11` went 534.6 MB → 13 148.3 MB with
every limit satisfied. **#536 then budgeted that working set and #575 took the 2x2 over both flags,
and both defaults moved.** `F4Options::recommended()` now carries `reduce_batch_rows: true` and
`InterreductionRoute::ByOrder`, which on `mq-random-10` is **4 695.7 ms against Singular's
7 371.9 ms — 1.57x ahead**, where the configuration M27 opened with was 3.74x behind, and on
`katsura-11` **1.80x ahead**. The memory objection dissolved rather than being overridden: the pair
costs **418.8 MB** where the route alone cost 602.9 MB, because the closure it no longer builds was
the cost.

**Two strategy flags now sit off by default in that position, not one.** #477 found that the 80%
interreduction share is a debt the *main loop* accrues — candidates are extracted from an echelon
form that was never back-substituted, so every batch emits elements whose tails are still
reducible — and `F4Options::reduce_batch_rows` pays it where it is incurred. That takes the final
autoreduce matrix from 7 642 x 7 996 to **252 x 606**, which is Groebner.jl's 250 x 604 to within
six columns, and the stage from 2 400 ms to **16.4 ms**. On the shipping division route it is
**4.92x** end to end — more than `interreduce_by_matrix` is worth on its own — and the two together
are **6.54x**. Unlike that flag it regresses no classical rung, including the katsura-5 lex case
that costs the matrix route 25x. **#575 moved both defaults together**, on the 2x2 as a five-engine board cohort — §3g of
[`docs/research/interreduction-cost.md`](../research/interreduction-cost.md). They are not
independent: with batches left reduced the autoreduce matrix is 252 x 606 rather than
7 642 x 7 996, and that closure is where the route's memory went, so `matrix` + `reduced` costs
**418.8 MB** where the route alone cost 602.9 MB. On `katsura-11` the route *alone* is now worth
nothing — #536's budget refuses its pass and it falls back — while the pair is **8.10x**. So
neither flag could have been decided without the other.
