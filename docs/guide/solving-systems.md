# Solving polynomial systems

Zero-dimensional solving end to end: the lex route, FGLM conversion, resultants, solution
verification, and how the solver chooses a route.

`grobner::solve` finds every point of F^N at which a system of multivariate polynomials
vanishes, over a finite field F:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp13, grobner::solve, MultivariatePolynomial};

let vars = ["x", "y"];
let system = vec![
    MultivariatePolynomial::<2, Zp13>::parse("x + y", vars).unwrap(),
    MultivariatePolynomial::<2, Zp13>::parse("x*y - 1", vars).unwrap(),
];

let mut rng = StdRng::seed_from_u64(0);
for point in solve(&system, &mut rng) {
    println!("x = {}, y = {}", point[0], point[1]);
}
```

It computes a lexicographic Grobner basis, which is triangular, then assigns variables from the
last backwards. At each step the basis polynomials that have become univariate in the current
variable are solved with `roots`, so only their common roots are tried. An inconsistent system is
detected from its basis being `{1}` and yields no points. The order of the returned points is
unspecified.

A system with finitely many solutions therefore needs no enumeration, and works over fields far
too large to list — the tests cover GF(2^31 - 1) and the largest 64-bit prime.

A system that leaves a variable unconstrained is the exception. Its solution set grows with the
field, so covering a free variable means enumerating, and `solve` refuses above an order of 2^20.
That is a limit on the size of the answer rather than on the method.


## Solving zero-dimensional systems

`grobner::solve_one` finds one solution and stops; `grobner::solve_zero_dimensional` finds every
distinct one. Both refuse a system that is not zero-dimensional rather than enumerating the field,
and both report every failure as a `Result`:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::fields::Zp2147483647;
use zeebra::grobner::{solve_one, SolveError};
use zeebra::{MultivariatePolynomial, Zero};

type F = Zp2147483647;
let mut rng = StdRng::seed_from_u64(1);

// Two equations, two unknowns, finitely many solutions.
let system: Vec<MultivariatePolynomial<2, F>> = ["x^2 - 4", "y - x"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
    .collect();
let point = solve_one(&system, &mut rng).unwrap().expect("a solution exists");
assert!(system.iter().all(|p| p.eval(&point).is_zero()));

// A curve has infinitely many solutions, so it is refused rather than enumerated.
let curve: Vec<MultivariatePolynomial<2, F>> =
    vec![MultivariatePolynomial::parse("x*y - 1", ["x", "y"]).unwrap()];
assert_eq!(solve_one(&curve, &mut rng), Err(SolveError::PositiveDimensional));
```

`Ok(None)` means the system is zero-dimensional and has **no solution over the base field** — which
is an answer, not a failure. `x^2 + 1` over GF(3) has quotient dimension two and no point in GF(3).
Only `Err` means the computation could not be completed, and `SolveOptions` bounds it: search
branches, returned solutions, and the F4 and FGLM limits underneath. An exceeded budget is an error
rather than a truncated list.

### Which answer, and what it cost

`Ok(None)` collapses two different answers: the equations may contradict each other, or they may
simply have no base-field solution while the variety is nonempty over an extension.
`solve_one_with_outcome` separates them and returns the diagnostics alongside:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp2147483647, grobner::{solve_one_with_outcome, SolveOptions, SolveOutcome},
             MultivariatePolynomial};

type F = Zp2147483647;
let parse = |s| MultivariatePolynomial::<2, F>::parse(s, ["x", "y"]).unwrap();
let options = SolveOptions::default();

// 1 is in the ideal: the equations contradict each other.
let contradiction = vec![parse("x - 1"), parse("x - 2")];
let (outcome, _) =
    solve_one_with_outcome(&contradiction, &mut StdRng::seed_from_u64(1), &options).unwrap();
assert_eq!(outcome, SolveOutcome::Inconsistent);

// 2^31 - 1 is 3 mod 4, so -1 is not a square: zero-dimensional, and no point in the field.
let no_point = vec![parse("x^2 + 1"), parse("y")];
let (outcome, statistics) =
    solve_one_with_outcome(&no_point, &mut StdRng::seed_from_u64(1), &options).unwrap();
assert_eq!(outcome, SolveOutcome::NoBaseFieldPoint);

// And what the route cost, which `solve_one` discards.
assert!(statistics.f4.is_some());
```

Every `SolveOutcome` variant is an answer; a crossed budget is still an `Err` and can never appear
as one. `SolveStatistics` carries the Gröbner stage's `F4Statistics` and, on the converting route,
the `FglmStatistics`, with `estimated_peak_bytes` the larger of the two stage estimates. That
figure is an estimate of the *representation* — on katsura-7 under lex it is 320 MB against a
measured 1,303 MB of process RSS, so use `util::peak_resident_bytes` when the question is about the
process.

### Structural analysis, which decides nothing

`grobner::analyze` reads a system's shape off its terms without computing anything:

```rust
use zeebra::{fields::Zp2147483647, grobner::analyze, MultivariatePolynomial};

type F = Zp2147483647;
let system: Vec<MultivariatePolynomial<3, F>> = ["x*y - 1", "x^2 - z"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, ["x", "y", "z"]).unwrap())
    .collect();

let shape = analyze(&system);
assert_eq!(shape.quadratic_generators, 2);
assert_eq!(shape.occurrences, vec![2, 1, 1]);      // per variable, generators it appears in
assert!(!shape.constant_contradiction);
// Least-constrained variable first. A ranking, not a recommendation.
assert_eq!(shape.specialization_candidates(), vec![1, 2, 0]);
```

`constant_contradiction` is the only sound conclusion in `SystemShape` — a nonzero constant
generator puts 1 in the ideal by itself. **Nothing else there bounds the quotient dimension or the
solving degree.** In particular `generators == variables` proves nothing: cyclic-4 is four
equations in four variables and positive-dimensional, katsura-4 is four in four and
zero-dimensional, and the two agree on every column `analyze` reports.

### Letting the solver choose

`solve_one_planned` picks a route on stated grounds and, if permitted, tries the other one — with
a decision log beside the answer. It is opt-in: the explicit entry points above are untouched.

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp2147483647, grobner::{benchmark_systems::katsura, solve_one_planned,
             PlannedSolveOptions, SolveOutcome, SolvePolicy}};

let options = PlannedSolveOptions::with_policy(SolvePolicy::AutoWithFallback);
let (outcome, plan) = solve_one_planned(
    &katsura::<7, Zp2147483647>(),
    &mut StdRng::seed_from_u64(1),
    &options,
);

assert!(matches!(outcome, Ok(SolveOutcome::Point(_))));
assert_eq!(plan.attempts.len(), 1);              // the opening route worked
println!("{}", plan);                            // every decision, with its reason and its cost
```

**The conservative opening is grevlex-then-FGLM**, which contradicts `DirectLexF4` being the
`#[default]` strategy described as "the conservative choice". The argument is not that conversion
usually wins — it loses on the whole planted family — but that **its refusals are cheap by
construction**: FGLM's binding budget is the span's `D² + D(D+1)` cells, computed from `D` and
checked before anything is allocated, while F4's is discovered during elimination and so costs the
whole elimination up to the crossing. Measured: katsura-7's direct attempt burns 28.3 s and 1.3 GB
before refusing; planted-12's conversion refuses after 36 ms. The conservative question is not
which route usually wins but **which route's failure is affordable**.

The one decision made on a measured quantity is the conversion's feasibility: after a source basis
exists, `D` is *counted* and the span requirement is a function of `D` alone, so
`SolveError::ConversionInfeasible` means the conversion was never started — distinct from
`Fglm(SpanStorageExceeded)`, which means it ran and crossed the limit.

`PlanBudget` is shared across attempts, and holds only quantities that are *spent* —
`max_elapsed` and `max_total_batches`. A peak is not consumed by an attempt, so the entry and byte
budgets stay per-attempt in `SolveOptions`. `SolvePlan` keeps the same split: `total_batches()`
sums, `peak_estimated_bytes()` maxes. `max_elapsed` is checked *between* attempts, since F4 has no
cooperative time check, so it bounds whether a second route starts rather than how long the first
runs.

An `Err` from the planner means **inconclusive**, never "no solution".
`cargo run --release --example solve_auto` compares all four policies against an offline
best-of-two the planner was not allowed to see.

### Underdetermined systems, and what a slice establishes

The zero-dimensional solvers refuse a positive-dimensional system, which is the right answer — but
the interesting cryptanalytic systems are underdetermined, so `grobner::research` fixes some
variables and solves the slice:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{fields::Zp2147483647, grobner::{research::{solve_slice, Specialization},
             PlannedSolveOptions}, FiniteField, MultivariatePolynomial};

type F = Zp2147483647;
// A curve: one equation, two unknowns, so positive-dimensional.
let curve: Vec<MultivariatePolynomial<2, F>> =
    vec![MultivariatePolynomial::parse("x*y - 6", ["x", "y"]).unwrap()];

let slice = Specialization::new(&[(0, F::new(2))]).unwrap();
let (outcome, _plan) = solve_slice(
    &curve, &slice, &PlannedSolveOptions::default(), &mut StdRng::seed_from_u64(1),
);
assert_eq!(outcome.unwrap().witness(), Some([F::new(2), F::new(3)]));
```

The slice ideal is `I + <x_i - a_i>`, **not** the substituted generators alone. Because `const N`
is not replaced, a fixed variable does not leave the ring — substitution only removes it from every
monomial, and a variable in no generator is *unconstrained*. `x*y - 6` at `x = 2` substitutes to
`2y - 6`, whose zero set in `F[x, y]` is the line `{(x, 3)}`. So `Specialization::apply` appends
the pinning equations, which generate the same ideal and make the fixed coordinates part of the
answer.

`SliceOutcome` has three variants where a solver has `Option`, and only one of them says anything
about the system you started with:

| outcome | about |
|---|---|
| `Witness(p)` | the **original** system — verified against every original generator |
| `EmptySlice` | this slice: zero-dimensional, no base-field point |
| `SliceInconsistent` | this slice: `1` is in `I_a` |

**A run of dead slices proves nothing.** A section of a nonempty variety can be empty over `F_q`,
and only exhausting all `q^|S|` slices would settle it.
`SliceOutcome::is_evidence_about_the_original_system` returns true for exactly one variant so that
a caller has to pass through it rather than reason about the variants.
`cargo run --release --example specialize_slices` runs ten slices at each of two sizes on one
system — seven witnesses at three fixed, ten dead at six fixed — which closes the argument with
evidence on both sides rather than asserting it. Each slice comes from its own seed, and
`Specialization::seeded` builds the RNG from it, so `seed()` is a promise that the slice
reconstructs; `Specialization::new` takes chosen values and records no seed.

### Reduced-round Poseidon

`grobner::research::Poseidon` is a port of the 2026 initiative's own cryptanalysis tooling
([`poseidon-tools`](https://github.com/khovratovich/poseidon-tools), Apache-2.0, commit
`60075da7`): KoalaBear, `alpha = 3`, the Grain LFSR round constants, the Cauchy MDS construction,
and the `permutation_plus_linear` variant the CICO verifier uses. **Not toy substitutes**, and that
is checkable rather than asserted — the reference's README records
`permutation([0]*16)[0] == 1393439926` at `t=16, R_F=8, R_P=20`, and the port reproduces it in a
committed test. That one number exercises the LFSR's bit layout, all 448 round constants, the MDS
construction, and the round schedule.

One vector anchors one configuration, though, and the round schedule changes with `R_F` and `R_P`
— so **every** configuration the corpus uses is also checked against vectors generated by the
Python reference, across the whole output state and in both permutation variants.
`Poseidon::new` is bounded on `KnownOrder` and refuses a coefficient type that is not the
parameters' field; `CicoInstance` requires exactly `2k` constants and an exact `N`, since a spare
position is an unconstrained variable that makes the ideal positive-dimensional.

`CicoInstance::system` generates the polynomial system. **Every S-box output is a fresh variable**,
so with `L` the affine form reaching an S-box the equation is `y - L^3 = 0` — degree 3 and no
more, where carrying state words as polynomials would give `3^rounds`. Round constants and the MDS
layer contribute no equations at all; they are affine.

Faithfulness is checked three ways: the system must vanish at a real trace of the permutation
(`verify_against_trace`); corrupting a trace value must break that value's own equation and no
*earlier* one; and any recovered input is verified by running the permutation on it
(`CicoInstance::is_solution`), not by re-evaluating the system. A generator bug cannot make the
last one pass.

Measured frontier, `k = 1`, planted targets:

| reduced to | variables | outcome |
|---|---:|---|
| `t=2 R_F=2 R_P=0` | 5 | solved, 0.8 ms |
| `t=2 R_F=2 R_P=2` | 7 | solved, 156 ms |
| `t=2 R_F=4 R_P=0` | 9 | solved, 371 ms |
| `t=3 R_F=2 R_P=1` | 9 | column budget crossed after ~18 s |

**Variable count does not predict reach** — but the reason is not the state width. `N - E = t - 2k`,
so at `k = 1` the `t = 2` rows are square and the `t = 3` row has one more variable than equation:
the two nine-variable instances are *not the same kind of system*, and the comparison above is
confounded. Controlling for it, by pinning a single free input of the `t = 3` system — which matches
the equation count without touching the round structure — it becomes **the easiest of the three**:
complete in 13.9 ms at degree 5 and 0.2 MB, against the square `t = 2` instance's 367 ms and 3.8 MB,
where unpinned it crossed the column budget at degree 11 and 155 MB.

So what the frontier measures is the underdetermined direction: one free coordinate takes the
computation from degree 5 to degree 11 and from 0.2 MB to 155 MB. The pinned system's dimension is
read from `classify_ideal` of its computed basis rather than inferred from the counts, and the
pinned value is a *planted* one, so a solution is known to exist on that slice — comparing it
against an arbitrary-target CICO challenge would be comparing different distributions. See
[`docs/research/degree-profiles.md`](../research/degree-profiles.md) §4.

The bounty instance is `t = 16, R_F = 6, R_P = 8`: 104 S-box variables and 118 in total. **No
result on a reduced instance says anything about the full one**, which is why
`CicoInstance::reduced_from` carries the parameters an instance reduced from.

The bounty's *relaxed* CICO verifier is **not** modelled. Its condition is on the low bits of a
field element's canonical integer representative — `(y - c) & mask == 0` — which is not a
polynomial identity over the field. See `docs/research/poseidon.md`.

#### Relabelling the variables, and getting the answer back

Which variable is `x_0` changes the Gröbner basis, the matrices and the cost, while changing nothing
about the problem — so variable order is a free parameter of a cryptanalytic experiment.
`research::VariableOrder` makes exploring it safe:

```rust
use zeebra::{fields::Zp2147483647, grobner::{benchmark_systems::planted,
             research::{satisfies, VariableOrder}}, FiniteField};

let point = [Zp2147483647::new(7), Zp2147483647::new(11), Zp2147483647::new(13)];
let system = planted::<3, Zp2147483647>(&point);

// sources[new] = old, checked to be a bijection of 0..N.
let order = VariableOrder::<3>::new("reversed", &[2, 1, 0]).unwrap();
let relabelled = order.apply(&system);

// The plant, moved into the new coordinates, solves the relabelled system — and comes back.
let moved = order.forward(&point);
assert!(satisfies(&relabelled, &moved));
assert_eq!(order.recover(&moved), point);
```

The constructor is the only way in and it rejects anything that is not a bijection, because a
non-bijective "permutation" silently identifies two variables and changes the problem. `recover` is
the only way back, and using `forward` in its place produces a point that satisfies nothing — which
on a system whose answer is not known in advance is indistinguishable from a solver that found
nothing. `RoundLayout` builds the three layouts the Poseidon experiments compare, from the
**per-round** S-box variable counts rather than one width, since a schedule mixes full rounds
introducing `t` variables with partial rounds introducing one.

#### Eliminating the variables an affine generator determines

A CICO instance's `k` output constraints are affine and nothing else in the system is.
`research::eliminate_affine` solves each affine generator for its highest-indexed variable and
substitutes, recording an affine expression in the **surviving** variables for each one eliminated.

**Substituting is not enough, and the reason is worth stating.** F4 already reduces by an affine
basis element; what it cannot do is make the variable stop existing, so it keeps a column in every
Macaulay matrix and a place in the monomial order. Worse, after substitution the variable appears in
no generator — so it is *unconstrained*, and the ideal becomes positive-dimensional. That is the
same trap `Specialization::apply` documents. `AffineElimination::project` removes the variables from
the ring at a smaller compile-time dimension, and `lift` puts a solution back; the dimension is
checked to be exactly the number of survivors, since a spare position is another unconstrained
variable.

The sweep is deliberately bounded: it is Gaussian elimination on the affine part of a generating
set, not a general preprocessor and not nonlinear elimination. An affine relation that appears only
after some nonlinear cancellation is not found, and nothing looks for one. A generator that
substitutes to a nonzero constant is **kept**, so an inconsistent system still reports `{1}`.

### The challenge registry

`grobner::research::registry` is the frozen list of public problems this project measures itself
against: the three 2026 Poseidon-31 CICO targets, a nine-row faithful reduced-round ladder at the
official state width, the small planted surrogates M21 and M22 measured, and the Fukuoka GF(31)
toy examples. A `ChallengeManifest` says what a **problem** is — objective, parameters, target, and
how a claimed answer is checked by something that is not this crate — where an `InstanceManifest`
says what a *file* is.

Three things keep it honest.

**`BenchmarkClass` is part of every row.** A witness for a `t = 2` planted instance and a witness
for the official `t = 16` target are both "solved" in a column that adds them together, and they
are not comparable in any direction. `Significance` is therefore *computed* from the class and the
external status rather than written by a report:

```rust
use zeebra::{fields::PrimeFieldElement64, grobner::research::{
    challenge, BenchmarkClass, ExternalStatus, Significance, KOALABEAR_PRIME}};

type K = PrimeFieldElement64<KOALABEAR_PRIME>;

let official = challenge("poseidon31-cico-rf6-rp8").expect("registered");
assert_eq!(official.class, BenchmarkClass::Official);
assert_eq!(official.external, ExternalStatus::SolvedExternally { verified: "2026-05-06" });

// 14 free inputs and 16·6 + 8 S-box variables, against those plus two output constraints.
assert_eq!((official.variables(), official.equations()), (Some(118), Some(106)));

// The strongest claim available on a challenge that is already solved publicly.
assert_eq!(official.significance(true),
           Significance::Reproduction { externally_verified: "2026-05-06" });
assert_eq!(official.significance(false), Significance::NoWitness);

// A reduction's witness is a real result about a different problem, and says so.
let reduced = challenge("poseidon31-cico-t16-rf2-rp0").expect("registered");
assert_eq!(reduced.significance(true),
           Significance::ReducedInstanceWitness { of: "poseidon31-cico-rf6-rp8" });

// The registry is executable: a runner takes its instance from here, so there is no second copy
// of the constants to drift from these.
let instance = official.cico_instance::<K>().expect("builds");
assert_eq!(instance.variables(), 118);
```

**`DisclosedMethod` is separate from `ExternalStatus`.** A program can verify a submission without
naming the submitter, and a paper can describe an attack at the same parameters without being that
submission — so "verified on this date" and "this is how it was done" are two claims, and the
registry keeps them apart:

```rust
use zeebra::grobner::research::{challenge, DisclosedMethod};

// The R_P = 8 target was solved by a univariate route, published by Sanso and Vitto.
let rp8 = challenge("poseidon31-cico-rf6-rp8").expect("registered");
match rp8.method {
    DisclosedMethod::Published { method, attributed_to_submission, .. } => {
        assert!(method.contains("Graeffe"));
        // The program does not name first submitters, so this is an attack at the same
        // parameters and not, on the present evidence, *the* verified submission.
        assert!(!attributed_to_submission);
    }
    other => panic!("expected a published method, got {}", other),
}

// R_P = 10 is solved and verified externally, and no method has been published. `Unknown` is the
// honest value; it is not a synonym for brute force or for anything else.
let rp10 = challenge("poseidon31-cico-rf6-rp10").expect("registered");
assert_eq!(rp10.method, DisclosedMethod::Unknown);
```

Disclosing a method never changes a problem's identity, which
`test_disclosing_a_method_does_not_change_identity` pins.
[`docs/research/elimination-beyond-grobner.md`](../research/elimination-beyond-grobner.md) §2 has
every published method and its reported cost.

**Identity is a digest over the problem, not over the paperwork.** `ChallengeManifest::digest` is
SHA-256 of a canonical form covering the family, the objective tag, the parameters and the target.
A corrected URL, a paid bounty or a reworded verifier leaves it alone; a changed round count does
not. That is what lets a comparison refuse to compare two runs of *different mathematical
problems*, which is the one failure a benchmark harness cannot be allowed to make quietly.

**The generator is pinned separately.** A parameter checksum cannot notice a changed generator: if
the Grain LFSR or the Cauchy construction changed, every registered instance would become a
different permutation with an unchanged identity. `derived_digest` hashes the round constants and
MDS matrix, and three of them are pinned in tests.

`dispatch_cico` bridges the const generic — `CicoInstance::system::<N>()` needs `N` at compile time
and the registry has fifteen distinct `N` — in the same shape as `MqVisitor` does for the MQ family.

**There are two manifest schemas, not one, and that was the decision rather than the accident.**
A `ChallengeManifest` says what a *problem* is; an `InstanceManifest` says what a *file* is, and a
challenge need not be a file — the 2026 CICO targets are a sentence and five numbers whose round
constants are derived rather than published. They share no field set and no conversion, and they do
share a convention set: one `Claim` tag for proved-against-observed, one float-free JSON writer, one
canonical-lines-then-SHA-256 idiom, and a `redistribution` field on each.
[`docs/research/benchmark-schema.md`](../research/benchmark-schema.md) is the written schema — the
three identity layers, #73's nine fields mapped onto the four types that carry them, and the eleven
things the schema deliberately refuses with the reason for each.

**A registered problem need not be one this crate can build.** The initiative ran two bounty
programs with objectives at opposite ends of the state — the 2026 CICO program constrains the
leading words, the 2025 program the trailing ones — and three 2025 tiers are still listed as
unsolved. Those are registered, and `cico_instance` and `dispatch_cico` **refuse** them by name:
building a trailing-constraint objective as a leading-constraint one would produce a different
problem wearing that row's identity, and nothing about the result would look wrong. A scoreboard
that listed only what it can run would hide the only open problems on it.

The registry is frozen by `test_the_registry_is_frozen`, which pins every id and digest, so
redefining a registered problem fails a test rather than silently changing what an earlier
measurement meant. See
[`docs/MILESTONE-CRYPTANALYSIS-SCOREBOARD.md`](../MILESTONE-CRYPTANALYSIS-SCOREBOARD.md) for the
full table and for what the three 2026 CICO targets' external status implies about what a result
there could claim.

### The scoreboard

`grobner::research::Scoreboard` collects what runs established about registered problems, and its
job is to refuse three specific mistakes.

**A recorded commit is not by itself a reproducible stamp.** A sweep is run on a branch and the
branch is merged, so `Environment::commit` names something that a history rewrite can leave
unreachable from `main` — which is what happened to 315 of the 387 competitive rows, and to two
cryptanalysis runs. `Environment` therefore records two more fields: `base_commit`, the merge base
against `origin/main`, which is an ancestor of `main` and stays one; and `patch_id`, `git patch-id
--stable` over `base_commit..commit`, which identifies the measured delta by its *diff* rather than
by a commit name and so survives the rebase or squash that invalidated the commit.
`Environment::stamp_is_resolvable` is the criterion — a base equal to the commit, or a base plus a
patch id — `Environment::from_git` fills all three, and one test per board asserts every committed
row passes. Records written before the fields existed read back with both empty, which reports as
unresolvable; that is the fact about them and not a defect in the reader.

Such a record can be **repaired rather than re-run**, but only while the branch commit is still an
object in some checkout — a dangling commit is reachable by name until `git gc` collects it, and
both fields are derivable from it:

```bash
git cat-file -t <commit>                              # still here, or this is the point of no return
base=$(git merge-base <commit> origin/main)
git diff "$base..<commit>" | git patch-id --stable    # the patch_id to record
```

Write `base_commit` and that patch id to **both** places a run lives: `research/scoreboard/runs/<stem>.json`
and the matching entry of `research/scoreboard/results/history.json`. Repairing one and not the
other is the defect `tests/scoreboard_run_files.rs` exists to catch — the history has unit tests
over an `include_str!`, the per-run files had none, and #550 landed in exactly that gap.

This is a **backfill of what the writer would have recorded**, not a new claim, so it is honest only
when both reads come from the measured commit itself; a base inferred from the merge commit is
precisely the plausible-looking stamp `stamp_is_resolvable` exists to refuse.

Checking such a stamp against `main` has one trap worth naming. The range to compare is the
measured **code** delta, not the whole squash: a squash merge of a measuring branch also carries the
records the measurement produced, which were not in the tree it was taken from, so the whole-commit
patch id will not match while the per-file code ones do. The four `fukuoka-mq-{V,VI}-n24-seed0` runs
at `a3e5d66` are the worked example — three files, same patch id on the branch and on `main`.

**Comparing different problems.** A `RunRecord` references its problem by identity *digest*, not by
name. `Scoreboard::add` looks the problem up in the registry and refuses a run whose digest no
longer matches — the problem was redefined after the run, so the measurement is about something
else. `Comparison::of` refuses two runs of different problems outright, and deliberately does not
compare ids.

**Ranking unfinished runs.** `Scoreboard::best` returns verified witnesses only. Two computations
that crossed a budget at degrees 9 and 11 are not ordered: a higher degree is not nearer a
solution. Those appear in their own table, under a heading that says it is a diagnostic.

**Quoting a difference the hardware cannot resolve.** `Comparison::runtime_readable` is false inside
±20%, which is the band M22 declined to read on this machine. The comparison is still reported, with
the flag.

```rust
use std::time::Duration;
use zeebra::grobner::research::{
    challenge, Comparison, Environment, GrobnerFrontier, RunOutcome, RunRecord, Stage, StageCost};

fn run(id: &str, formulation: &str, millis: u64, bytes: usize) -> RunRecord {
    let manifest = challenge(id).expect("registered");
    let mut run = RunRecord::new(&manifest, formulation);
    run.outcome = RunOutcome::VerifiedWitness;
    run.stages = vec![StageCost::new(Stage::Grobner, Duration::from_millis(millis))];
    run.frontier = Some(GrobnerFrontier { completed: true, peak_estimated_bytes: bytes,
                                          ..GrobnerFrontier::default() });
    run
}

// Two formulations of one problem: M22-E's last-round-first result on this instance.
let baseline = run("poseidon-t2-rf4-rp0-planted", "as generated", 352, 3_800_000);
let candidate = run("poseidon-t2-rf4-rp0-planted", "last-round-first", 219, 2_900_000);
let comparison = Comparison::of(&baseline, &candidate).expect("the same problem");
assert_eq!(comparison.speedup_per_mille, 1_607);          // 1.607x, as two integers
assert_eq!(comparison.memory_reduction_basis_points, 2_369);
assert!(comparison.runtime_readable);

// A different problem is refused rather than rendered.
let elsewhere = run("poseidon-t2-rf2-rp2-planted", "as generated", 143, 1_700_000);
assert!(Comparison::of(&baseline, &elsewhere).is_err());
```

Costs are recorded **per stage** — generation, Gröbner, conversion, univariate, verification —
because M20 measured that over a wide field the cost is not in the matrices, and a single total
hides the stage that dominates. The runner therefore drives `f4_reported`, then
`fglm_to_lex_with_options`, then `solve_from_lex_basis` itself rather than calling
`solve_one_planned`.

A randomized specialization campaign is summarized by `Campaign`, which reports the slices that
found **nothing** alongside the one that worked: work per witness is the whole campaign's time over
the witnesses, and the success rate carries a 95% Wilson interval. One witness in twenty slices is
a rate of 0.89% to 23.6%, which is a different claim from "solved in 2 seconds".

```sh
tools/scoreboard.sh                    # smoke tier: the surrogates, nothing written
tools/scoreboard.sh stable --write     # adds the published MQ instances, updates the tree
tools/scoreboard.sh ladder --write     # the nine full-width t = 16 rows, one process each
tools/scoreboard.sh campaign poseidon31-cico-t16-rf2-rp0 --seeds 8 --write
tools/scoreboard.sh formulations poseidon31-cico-t16-rf2-rp0 --slice 1 --write
```

The full-width rows run one process each because the wall-clock supervisor stops a run by
abandoning its worker thread and exiting — F4 has no cooperative time check, so there is no other
way — and that is acceptable once per process and not nine times in one. The budget that actually
binds on those rows is the live-entry cap rather than the clock, which is deliberate: an entry
count is reproducible anywhere, a timeout is a fact about one machine.

**The first verified CICO witness at the official state width** came out of that harness:
`t = 16`, `k = 2`, KoalaBear, the challenge's own input constants, the exact objective, `R_F = 2`
and `R_P = 0`, with twelve of the fourteen free inputs fixed at a precommitted seed. Three of eight
slices produced a point that `permutation_plus_linear` accepts, at **81.2 s of expected work per
witness including the five that found nothing**. The official targets are `R_F = 6` with
`R_P ∈ {6, 8, 10}` and all three were solved externally in 2026; this is a witness for a registered
*reduction*, and the scoreboard says so in those words. See
[`docs/research/full-width-poseidon.md`](../research/full-width-poseidon.md) for the eighteen-row
ladder, where each row stops, and the formulation comparison — in which M22-E's winning variable
order turns out to be **2.4x worse** at `t = 16` than the layout it beat at `t = 2`.

The tree under `research/scoreboard/` is committed: the registry emitted from code, one JSON record
per run, the accumulated history, and a generated `SCOREBOARD.md`. `Json::parse` reads back what
`Json::to_json` writes — round-tripping is asserted — so the history accumulates rather than being
overwritten, with no dependency to read eighty lines of writer.

**Reading an `environment.policy` written before #469.** Those records say `400 MB live`, and the
budget that actually bound was **320 MB**: the runner set `max_live_bytes` to 400 MB and left
`max_live_nonzeros` at its default 20 000 000, and the effective limit is the `min` of the two
(#322) — 20 000 000 entries over the 16-byte entry every row on this board uses. So a
`stopped_at_limit` row from before #469 must be reconciled against 320 MB, not against the figure
its own policy string quotes. Nothing about those runs or their timings changed; the overstatement
was in the prose alone, which is why the records are left as emitted rather than rewritten by hand
(#334). Since #469 the string is derived from the options by `F4Options::live_budget_policy`, which
reports the allowance that binds and names the budget it came from, so the two cannot drift apart
again.

### The cost model: predicted against measured, with the difference attributed

```bash
cargo run --release --example cost_model                  # render research/cost-model/COST-MODEL.md
cargo run --release --example cost_model -- --write       # regenerate the register from its records
cargo run --release --example cost_model -- --write --seed  # append any transcribed row not yet held
cargo run --release --example cost_model -- --list-runs      # the retained runs a row can be emitted from
cargo run --release --example cost_model -- --write --from-runs <run-file-stem>
```

`grobner::research::cost_model` keeps one row per **claim** about what a stage would cost, against
what it cost. Every figure carries a `FigureBasis` — `Measured`, `Fitted`, `Predicted` or
`Extrapolated` — because the failure it exists to prevent is documented rather than hypothetical:
M24 found that every prediction about a stage already measured held, and every prediction about an
unmeasured quantity was wrong, three of four by more than an order of magnitude, because all ten
were written in the same prose with the same confidence. A `measured_` field holds only a measured
figure and a `predicted_` field never holds one; a row violating either does not load.

Three further rules are code rather than convention. **Peak allocated and peak resident do not
share a column**, since #237 measured 21 674 MiB allocated against 13 996 MiB resident on one row.
**The resource-limiting stage is a closed set**, so "memory" and "the monomial queue of one refused
batch" cannot be written in the same field. **Prediction error is derived** — nothing in
`research/cost-model/results/history.json` is an error column, and `CostRow::prediction_errors`
computes it from the predicted and measured fields. **A row is emitted by a run rather than
transcribed from one.** `CostRow::from_run` reads a retained `RunRecord` — its stage runtimes, its
total, its measured peak, its frontier's work counts — and `--from-runs <run-file-stem>` appends a
row for each **named** run the register does not already hold, idempotently and append-only.
Transcription was how #294 got twenty rows of history onto the board and the wrong way to keep it
there: the next figure reaches the board only if somebody remembers to copy it.

**The register is curated, and the emission has no sweep** (#532). `select_runs_by_stem` refuses a
`--from-runs` with no run named, and `--list-runs` is the read-only way to find a stem, because
emitting a row per retained run is both undesirable and not expressible:

- An emitted row carries **no prediction**, so `CostModelBoard::open_predictions` — "the register's
  most useful view", and the one §10.1's finding is about — ignores it, while `to_markdown` still
  renders it in the per-algorithm table. Sweeping the addressable runs would add nothing to the
  view the register exists for and swamp its 23 curated rows several times over. `research/scoreboard/` is
  already the complete measured record; this board is about whether the predictions held.
- A row's `source` is its only link back to evidence, and for an emitted row that is
  `research/scoreboard/runs/<stem>.json`. **#540 has since made that citation always resolve**: the
  stem is now `challenge--formulation--commit--<digest>`, where the digest is SHA-256 over the
  record, so a re-measurement no longer replaces its predecessor's file and
  `research/scoreboard/runs/` holds one file per retained run — 105 files for 105 runs, where before
  it held 89 for 105 and the two sets of 89 were not even the same set. So the second reason above
  no longer holds: a row per run **is** expressible, and the emitter's idempotence check on
  `(key, source)` can now distinguish a second run from its own previous output.

  The register stays curated anyway, on the first reason alone, which is a judgement about what the
  board is *for* rather than a limit of the record tree. Reconsidering that is #532's decision to
  revisit, not something #540 changed by itself.

What an emitted row **may not** claim is the more interesting half, and all three rules are code:

- **No predicted field, including `peak_estimated_bytes`.** That field is the predicted half of the
  `accounted storage` pair, so filling it beside the measured RSS would make the row complete and
  oblige the adapter to attribute the gap — and a defaulted attribution would make every emitted row
  report that a prediction held, which inverts the register's purpose. The attribution stays
  `NoMeasurementYet` and a later pass supplies the prediction it was checking.
- **No limiting stage inferred from the budget that was crossed.** `LimitingStage::NotEstablished`,
  always. #237 is why: `max_live_nonzeros` was the budget crossed and 88.4% of the peak was the
  symbolic queue, which holds no matrix at all.
- **No peak it cannot attribute.** `VmHWM` from a process that ran several rows is a ceiling over
  all of them, so the figure is emitted only when `RunRecord::measured_peak_is_attributable` holds.

`tools/scoreboard.sh --write` deliberately does **not** call the emission. #334's complaint was that
a new measurement reaches the register only if somebody remembers; the answer to that under a
curated register is that a new measurement reaches `research/scoreboard/` automatically and reaches
*this* board when a prediction wants checking against it, which is a judgement the runner cannot
make.

The history is append-only: a re-measurement is
a new row with a new commit, which is what keeps #318's three figures for the same measurement all
visible — and that append-only rule is what let #318 be resolved, since the way to find out whether
a figure still holds is to re-run the binary that produced it and record the answer beside the
original rather than over it (`docs/research/resultant-elimination.md` §6.13).

### Elimination that is not a Gröbner basis

`grobner::research::bivariate_resultant` computes `Res_y(f, g)` for two bivariate polynomials, as
the determinant of their Sylvester matrix recovered by interpolating scalar determinants;
`bivariate_resultant_ntt` computes the same resultant with the samples taken on a power-of-two
subgroup, so the recovery is an inverse NTT rather than a cubic solve. The
determinant construction needs no case analysis: evaluating a matrix and taking its determinant
commutes with evaluation *always*, where specializing `f` at a point that kills its leading
coefficient in `y` drops its degree, and the specialized resultant is then not the specialization of
the resultant.

**Which per-sample kernel evaluates that scalar is now a choice**, `ResultantOptions::kernel`:

- `DeterminantKernel::Dense` — dense LU on the `(m + n)`-square matrix, `O(n³)`. The **default**, so
  a figure taken before the alternative existed reproduces unchanged.
- `DeterminantKernel::Euclidean` — `poly::resultant_from_coefficients`, driving `f mod g` down the
  polynomial remainder sequence in `O(n²)`.

Both return the same scalar, including at the specialization points, where the fixed Sylvester order
and the fallen true degrees differ by a correcting power of a leading coefficient — the case analysis
the dense route avoids, closed in `O(1)` per sample by `poly::resultant_at_formal_degrees` and
asserted against an explicitly built determinant over all 15 625 degree-drop combinations. Measured
same-binary on one pinned core, the Euclidean kernel is **137× faster at order 162 and 2 094× at
order 1 458**, with fitted exponents of **2.94** and **1.85** — the ratio grows with the order
because the kernels differ by a power of it. It does **not** raise the reachable round count: the
six-round route becomes 78% root finding, so the row gains ~3×. See
`docs/research/structured-sylvester.md` §5.6.

It exists to answer one question, and the answer is worth knowing. On a registered `t = 16` CICO
slice — twelve of the fourteen free inputs fixed, two unknowns left — the S-box variables can be
*evaluated away* instead of solved for, because the permutation is a straight-line program. That
turns 46 equations in 46 variables into **two polynomials in two variables** of degree `3^rounds`,
and one resultant finishes it:

| route | time on the same slice | witnesses found |
|---|---:|---|
| grevlex F4, then FGLM, then the search | 30 142 ms | the first one |
| straight-line evaluation, then one resultant | **51 ms** | **all three** |

578x, on the same registered problem, with every candidate checked by running the permutation. The
S-box-per-variable formulation exists to hold the degree at 3 and pays 32 extra variables for it;
when only two inputs are free, those variables are the whole cost and the degree it avoids is
affordable.

**The four-round rows now complete, with verified witnesses** — `poseidon31-cico-t16-rf2-rp2` in
about 40 s and `-rf4-rp0` in about 41 s, where F4 stops at two rounds and this route previously did
too. Each witness is checked by `CicoInstance::is_solution`, which runs `permutation_plus_linear`;
the coordinates are committed under `research/witnesses/` and re-checked by the test suite. The
enabling change is #162 making `lagrange_interpolate` quadratic. The route's own limit is still
arithmetic — about `16 · 3^{5·rounds}` field operations, now almost entirely the determinants — so
six rounds remains `3.3 × 10^15` and out of reach.

`bivariate_resultant_ntt` moves where the samples are taken: the *same* Sylvester determinants on a
power-of-two multiplicative subgroup, recovered with one `fft::interpolate`, with
`interpolation_route` falling back to `bivariate_resultant_reference` on a field whose two-adicity
admits no domain — Mersenne-31's is 1. **Single-threaded it is measured slower than the reference,
by 1.23x–1.40x**: the sample count goes as `2d²` and each sample is an order-`2d` determinant, so
determinant work grows as `d^5` against a quadratic interpolation's `d^4`, and padding 13 123
samples up to 16 384 costs 10.4 s of determinants to remove 1.5 s of interpolation. Both routes are
retained and `examples/resultant_cico.rs` runs them side by side in one process.

**That sign flips under concurrency, and retaining both routes is why it could be seen.**
`ResultantOptions::concurrency` spreads the independent determinants over worker threads and
defaults to 1, so every figure above reproduces unchanged. The samples are written into their own
index rather than collected as they finish, so the recovered polynomial does not depend on the
worker count — asserted byte-identical, with the identical witness set, at 1, 8 and 32. Measured on
a 32-core pinned set under the benchmark lock, the four-round determinant stage runs at **92–95%
parallel efficiency out to 32 of this box's 128 cores**, taking `rf2-rp2` end to end from 49.7 s to
**2.16 s**. The shortfall is the all-core clock and not bandwidth: per-determinant core time steps
up 4% once eight cores are busy and is then flat to 32, and the live working set is 27 MB against a
256 MB L3. The subgroup route then *wins* by 1.7–1.8x, because its extra determinants parallelize
and the reference route's 1.6 s Lagrange solve does not — at 32 workers the reference route is more
than half serial interpolation.

Timings carry the concurrency onto the scoreboard rather than hiding it. `Environment::concurrency`
is recorded on every run and reads back as 1 for records written before it existed;
`Comparison::of` **refuses** two runs that disagree on it, with `DifferentConcurrency`, since the
ratio would be a core count rather than a speedup; and `Scoreboard::best` — the headline the
rendered table quotes — considers uncontended runs only, so a 30x of cores cannot displace the
single-core figure it is not comparable with. `Scoreboard::best_at` reaches the parallel rows on
purpose.

Two other results from the same run: the resultant's degree matches the **published, unproven**
`d^{2R_F+R_P}` on all three rows measured — 729 against a Bézout bound of 6 561 on the row with
partial rounds — and that makes the sample count predictable rather than merely loose. See
[`docs/research/resultant-elimination.md`](../research/resultant-elimination.md).

`bivariate_resultant_predicted` acts on that. `predicted_resultant_degree(alpha, r_f, r_p)` returns
`alpha^(2 R_F + R_P)` from the instance's own parameters, and the route samples one point more than
that rather than the Bézout-sized `2d²` — **730 determinants instead of 13 123** on
`poseidon31-cico-t16-rf2-rp2`, and 6 562 instead of 13 123 on `-rf4-rp0`. Against the 16 384 the
subgroup route used by default those are 22.4x and 2.5x. The predicted count is not a power of two,
so it pairs with arbitrary-point Lagrange and not with an NTT domain, which would round 730 up to
1 024 and return a third of the saving.

The formula is **experimental and unproven in its source**, so the route validates rather than
trusts it: the recovered polynomial is checked against a direct Sylvester determinant at points the
interpolation never sampled, the check is part of the route rather than a flag —
`ResultantOptions::with_off_domain_checks(0)` panics rather than disabling it — and on disagreement
the proven `2d²` path produces the answer with `DegreeSource::PredictionFalsified` recording that
the published formula did not hold on that row. A falsification would be a result worth more than
the samples it saved, so it is recorded rather than silently repaired.

The check's own determinants go over the **same** worker pool as the interpolation's samples:
`off_domain_abscissae` is pure in the sample count and the fixed seed, so the points are drawn
before anything is evaluated and then partitioned through the one indexed `sample_determinants`
loop. At order 1 458 eight checks measure 19.97 s serial against 2.82 s at eight workers, which
takes a six-round row's validation share from 3.1% to 0.5%. Every check is evaluated before any is
compared, so the verdict cannot depend on which worker finished first, and the draws are distinct
rather than merely off-domain. It remains a **probabilistic consistency check and not a proof of a
polynomial identity** — eight agreements bound the failure probability by `(bound/p)^8`, which is
`4 × 10^-27` at six rounds: overwhelming evidence, and not the certificate that the proven-bound
routes get from uniqueness of interpolation.

`examples/resultant_cico` selects what it attempts: `--row <challenge-id>` (repeatable),
`--max-samples` and `--wall-budget`, with a row over either **costed and skipped** and its
arithmetic printed. `--build-only` times `cico_bivariate` alone, which is the bounded measurement a
row past the budget still supports. There is no `--all` — it removed the guard entirely, which put
a 12.9-day row beside a bounded one.

**`--wall-budget` is against the whole row, not against one stage of it.** Until #410 it costed the
Sylvester determinants and nothing else, which was defensible while those were ~99% of a four-round
row and stopped being so when #350 and #351 landed: they are **15% of an `rf4-rp2` row and 0.5% of
an `rf6-rp0` one**. `grobner::research::row_cost` is the model — pure and unit-tested, with the
determinant laws below moved into it unchanged — and it costs five terms, each printed with its own
basis (`measured` / `fitted` / `extrapolated` / `NOT MODELLED`) and the anchor behind it, so a
budget line cannot read as covering a row it covers a fraction of. The symbolic build is a
**recorded constant per round count** rather than a law (324.0 s at six rounds, measured on the
lock after #243) and interpolation is anchored on two measurements, 5.1 ms at 730 samples and 31.7 s
at 59 050. **Root finding is a band** — the gcd route pessimistic against deflation optimistic,
because its cost is `(roots + 1)` searches and the eliminant's base-field root count is a property
of the problem, `O(1)` on every registered row measured and unmeasured on every row nobody has
attempted — and the refusal is on the pessimistic edge. A row whose symbolic build nobody has
measured at its round count is refused as **unbounded** rather than admitted on the terms that are
modelled, because an unmodelled term is not a zero term. The default 1 800 s budget is unchanged and
admits the same rows. See
[`docs/research/resultant-elimination.md`](../research/resultant-elimination.md) §6.14, which also
records that the predicted band brackets #367's measured `rf4-rp2` row with the optimistic edge 1.2%
above it.

What the guard costs a row's determinants with is **measured rather than assumed**. `examples/determinant_sweep`
times the Sylvester determinant kernel at orders 18, 162, 486, 1 458 and 4 374 on random bivariate
pairs and fits a power law with per-point residuals, and the answer is piecewise: above the L2
footprint the exponent is **2.9953 ± 0.0285** with a worst residual of 3.7% — cubic to within the
measurement, including at order 4 374 whose 153 MB matrix exceeds a CCX's L3, so there is no cache
cliff to model — and below it 2.79, which is fixed per-determinant overhead the small orders cannot
amortize. `determinant_core_ms` takes the **larger** of the fitted and cubic laws, because 2.9953 is
below 3 and a cost model that under-predicts authorizes a run nobody costed, times a measured
core-time penalty for running wide (2.404 s, 2.821 s and 3.148 s a determinant at order 1 458 on 1,
8 and 32 workers). The six-round rows' **determinants** come out at 12.0 min (`rf2-rp4`), 1.79 h
(`rf4-rp2`) and 16.15 h (`rf6-rp0`) on 32 dense workers — the whole rows under the Euclidean kernel
are 5.5 min, 6.1–8.6 min and 49.3 min–3.61 h, §6.14 — and the eight-round rows at order 13 122 are
490 and 4 415 days of determinants, out of reach by three orders of magnitude rather than by a
factor the sample count could recover. See
[`docs/research/resultant-elimination.md`](../research/resultant-elimination.md) §6.9, which also
records that the figures on record are about 1.2x faster than the same measurements today, and that
the 2.868 ms order-162 anchor every earlier projection used does not reproduce.

**Why a figure does not reproduce, and what a ratio may be divided by.** §6.13 answers that, and
`examples/determinant_era` is the instrument: one source file written against the API that is
byte-identical across the commit range, so it compiles against an old library and a current one and
only the library beneath it differs. Checking out the commit a figure came from and re-running it is
what decides whether a stale figure indicts a commit or a session — and here it indicts the session:
§6.5's own binary gives 45 159.7 ms where its table says 37 634.3 ms, so **no commit can be
responsible and bisecting the range would land on nothing**. The effect is monotone in the working
set (nil at ~10 kB, 4–6% at 105 kB, 15–21% at ~840 kB), which excludes the clock. The usable output
is a bound: *an order-162 determinant figure reproduces to about ±10% within a session, ±20% across
sessions on an idle box, and no better than ~1.5x once other agents are building; ratios taken
inside one session reproduce to about 0.03.* The separate 31–44% width penalty of §6.9 was ambient
load alone — `tools/benchlock.sh` serializes benchmarks and not builds — and §6.6's 4–9% reproduces
on a quiet machine, so the lock now records `load=` on its START and END lines.

### External instances: the Fukuoka MQ Challenge

`grobner::research::MqInstance` imports instances from the
[Fukuoka MQ Challenge](https://www.mqchallenge.org/). **All six families import since #197**, each
at a named coefficient type: the GF(31) families (types III and VI) over `Zp31`, the GF(2^8) ones
(types II and V) over `Gf256Mq`, and the GF(2) ones (types I and IV) over `Zp2`. No new arithmetic
was needed for any of them — what each was waiting on was a decision or a parser, not a field.

GF(2) was the last refused, and **not for want of an export**: `binary_field` and `extension_field`
have been public since `8757b4a`, and that claim was stale here long after it stopped being true
(`docs/research/boolean-solving.md` §1). What it was actually waiting on was the choice between
`Zp2` and `BinaryFieldElement<0b11>`, decided as `Zp2` on storage in §8 of that document. With the
choice made the refusal had nothing left to protect: **the order alone identifies GF(2)**, since
there is exactly one field of order two, so unlike GF(2^8) there is no modulus to check.
`SUPPORTED_DIMENSIONS` is `[5, 10, 15, 20, 24]` — the union of the published toy sizes, which differ
per family (types I–III publish `n = 10, 15, 20` and types IV–VI `n = 5, 10, 15`), plus the smallest
real signature instance at `m = 16`. What blocks types I, II and IV at their *real* sizes is the
compiled dimension and, over GF(2), the 16-bytes-per-bit sparse entry — not the field.

GF(2^8) took three things, and they had to land together. The real header is
`GF(2)[x] / x^8 + x^4 + x^3 + x^2 + 1` rather than `GF(2^8)`, so no genuine file parsed at all.
Coefficients are two-digit **hex** bytes, and because 100 of the 256 bytes have an all-decimal
spelling, accepting the header without also switching the base would have turned a loud
`BadHeader` into a system silently built from different field elements — `MqField::radix` now
decides the base of a coefficient row and of an answer vector alike (#415 did the latter). And the
coefficient route is `KnownOrder::element_at`, not `FiniteField::new`: over an extension the trait
`new` is the prime-subfield embedding, so `Gf256Mq::new(0xa7)` is `1` and a byte-wise read through
it would collapse every coefficient to a bit.

The upside is bigger than the defect was. Because the header *states* the modulus,
`MqInstance::check_coefficient_field` **verifies** it against the coefficient type instead of
assuming one: it derives the type's own modulus from arithmetic and reports `MqError::WrongModulus`
on a mismatch, so `Gf256` (AES, `0x11B`) is refused for a challenge file and `Gf256Mq` (`0x11D`) is
accepted. No order comparison could separate them — the two fields have the same order.
[`docs/research/fukuoka-mq.md`](../research/fukuoka-mq.md) §2.4 settles which is right against a
published answer: all 20 polynomials of type II `n = 10` vanish under `0x11D` and none under
`0x11B`. Since #197 that is a **test** rather than a recorded observation —
`mq::tests::test_the_published_answer_vanishes_only_under_the_challenges_modulus` builds the AES
system by hand, because the checked path refuses it, and asserts the 20-versus-0 split. Isomorphic
fields of the same order cannot be separated by any shape or order check, so the challenge's own
answer file is the only oracle that distinguishes a correct import from a silently wrong one.

The coefficient layout is **every monomial of degree at most two in descending grevlex order**,
which is what the file's own `Order` header names. It is implemented by sorting with
`MonomialOrder::GradedReverseLexicographic` rather than as an index pattern, and it was *verified*
rather than assumed: four candidate layouts were evaluated at a published answer and exactly one
makes every polynomial vanish. A monomial-order translation error is the failure mode an importer
has, and it is silent.

On type III `n=10` seed 0 — 20 quadratics in 10 unknowns — zeebra reconstructs the system, confirms
it vanishes at the published answer, and independently recovers that same point in **111 ms** with
`D = 1`. Both directions matter: a wrong layout could vanish at one point by accident, but it could
not also be solved to the same one. This is a *toy* example 24 variables short of the smallest
published type III challenge, which starts at `n = 34` — not `n = 55`, which is type I's range —
and is not a competitive result.

**The importer now reaches the real challenge.** `SUPPORTED_DIMENSIONS` is `[10, 15, 20, 24]`, and
24 is where the toy examples stop being the only thing it can read: types V and VI publish
`m = 16..=35`, the generator truncates `n = m * 1.5`, and `m = 16` is `n = 24` in both — so one
`const N` arm serves the smallest real instance over GF(31) *and* over GF(2^8).
`fukuoka-mq-VI-n24-seed0` is registered with its file's SHA-256 and with the hall of fame's own
figure for it (Faugère, F5-FGb, 5 280 s, 2015), which makes a witness there a **reproduction** and
says so. The list stops at 24 deliberately: each entry monomorphizes the whole multivariate stack,
and a dimension that cannot be used is worse than `MqError::UnsupportedDimension` naming it.

One diagnostic slice of that instance — eight of the 24 variables fixed at a precommitted seed,
which is the challenge's own route for a signature type — **stops on live-entry growth at degree
6**: 20 010 753 entries against the 20 000 000 cap, largest matrix 13 602 x 19 132, 42 s. Type VI
`n = 15` crossed the same cap at degree *9*, so eight surplus variables rather than five pulls the
wall in rather than pushing it out; what grows is the width at every degree. A deliberate resource
stop, not a comparison with the published 5 280 s, and not a completion attempt.

**And the same size over the other field.** Type V publishes `m = 16` too, so `fukuoka-mq-V-n24-seed0`
is the same `n = 24` over GF(2^8) — registered, and runnable since the scoreboard's MQ visitors
became generic over the coefficient type and started dispatching on the instance's own field
rather than on a hardwired GF(31) (#510). The two slices **stop identically**, and did so
in three pairs at three commits: degree 6, the same 13 602 x 19 132 matrix, 4 967 pairs against
4 968, and 20 010 753 live entries against 20 011 556 — a difference of 803 entries in 20 million.
The wall is 44.3 s against **111.1 s**, so with the computation held fixed the field alone is about
**2.5x**. That is
the pair's value: §4.4's type VI-against-type III comparison varied the shape, and this one holds
the shape fixed and prices the arithmetic.
[`docs/research/fukuoka-mq.md`](../research/fukuoka-mq.md) §4.4 has the figures and the slice
policy: a slice result is a result about the slice, a witness lifts because the pinning forms are
part of the system, and a stopped slice establishes nothing about the instance.

Under one stated budget — 200,000 columns and 20,000,000 live entries, the bound that binds —
`n = 15` **recovers the published answer** in 7.9 s, checked coordinate by coordinate against the
answer file it was not given; `n = 20` crosses the entry cap at degree 5 after 67.5 s. So the
published type III examples end at `n = 15` here. Type VI `n = 15` needs a slice, and all eight
precommitted slices crossed the same cap at degree 9 — recorded as a campaign that **reached no
verdict** rather than as eight failures, because a slice that ran out of budget never tested
whether it contains a solution. `Campaign::decided()` is the rate's denominator for exactly that
reason, and `success_rate_basis_points` returns nothing when nothing was decided.

**The instance data is not redistributed here** — the files are "All Rights Reserved" with no
stated licence. `tools/fetch-mq-challenge.sh` fetches them into `research/instances/mq/` (the toy
examples, plus the two real `m = 16` challenges) and verifies the SHA-256 that `Provenance` and the
registry pin; the tests against genuine instances are `#[ignore]`d for the same reason the Singular
one is, and no instance bytes, answer vector or coefficient is committed. `docs/research/fukuoka-mq.md` records the format, the
verification, and one quirk worth knowing: coefficients are uniform over `0..=31`, not `0..=30`, so
**zero is twice as likely as any other coefficient** in the published GF(31) data.

That quirk is no longer an inference. The challenge publishes its own **coefficient generator**, and
every instance is reproducible from `(type, n, m, seed)` plus a 200 Mbit file of π it distributes —
confirmed against all six types' toy examples, coefficient for coefficient
([`docs/research/fukuoka-mq.md`](../research/fukuoka-mq.md) §7). **That generator is implemented**
(#420, `src/grobner/research/mq_generator.rs`): `tools/fetch-pi.sh` fetches and checksums the digit
stream once, after which an instance is a walk over it — `start = type * n`,
`interval = (seed + n) * 10 + type`, one coefficient per stride at the field's own width, with both
corrections the shipped verifiers need applied (§7.3).

```sh
tools/fetch-pi.sh            # fetch and verify PI, once; it serves every instance
tools/fetch-pi.sh --verify   # check what is already there
```

**Implementing it changed what the record says.** §7.3 had reported the shipped verifiers as broken
in two ways, from the toy examples; running the implementation against the real challenges showed
both "defects" are **parameters**, and that the published data falls into three classes:

| class | reads per polynomial | the value `31` | the constant column |
|---|---|---|---|
| toy examples, all six types | `mon - 1` | kept | **not** from π |
| real encryption, types I–III | `mon - 1` | **resampled** | **not** from π |
| real signature, types IV–VI | **`mon`** | resampled | **from π** |

Each row is zero mismatches against genuine files, every coefficient compared. So a **real signature
challenge needs no instance file at all** — `(type, m, seed)` plus `PI` rebuilds it exactly,
constants included, which settles a question `docs/research/fukuoka-mq.md` §7.4 had recorded as not
established and removes the redistribution problem for types IV–VI outright. A **real encryption
challenge** is rebuilt except for one column per polynomial, and that column is the planted answer
(`YDHTS15` Algorithm 1 Step 4), so `GeneratedMq::into_instance_with_constants` takes it from the
caller rather than inventing it.

`research/fukuoka-mq/solved-instances.tsv` records all **125** published solves, across all six
types — parameters, dates, solvers, algorithms, hardware and figures, with no instance data —
checked by `tests/fukuoka_mq_records.rs`. One row per detail page, in bijection: the 58-page count
of the previous revision was a pattern that dropped every page named for a second submission the
same day, and the page count and the solve count reconcile exactly once it is fixed
(`docs/research/fukuoka-mq.md` §14.2). Twelve of the 125 published figures are not wall-clock
totals — five per-subsystem, seven CPU-hour totals with no wall figure at all — and the fixture tags
each one rather than letting it be quoted as a record time.

### Candidate external instances, surveyed but not imported

[`docs/research/additional-benchmarks.md`](../research/additional-benchmarks.md) is the shortlist
of published cryptanalysis instances worth importing next, with the rejections and their reasons.
Four candidates are accepted: reduced-round **Anemoi** CICO, whose reference data is raw Magma F4
and FGLM logs under MIT and whose quotient dimension is a published `(α+2)^N` zeebra can be checked
against; reduced-round **Griffin**; Anemoi's `ACICO` model as a second formulation of the first; and
reduced-round **LowMC**, recorded there as blocked on `binary_field` not being exported — which it is
not: the module is public and LowMC is over GF(2), where the whole solve path works
(`docs/research/boolean-solving.md` §6). UOV, MAYO, Arion and
XHash8 are rejected, each with a recorded reason. The document also states plainly that the
[LowMC challenge](https://lowmcchallenge.github.io/) is a **claimed-complexity competition** — its
results are `log₂ T` and `log₂ M` estimates, several with memory exponents past 65 bits, and there
are no challenge files to solve.

An accepted candidate becomes a `ChallengeManifest` row, so the document also records what each one
would require of [the registry](#the-challenge-registry): an `AnemoiCico` parameters variant with
the algebraic model *inside the digest*, since `FCICO` and `PCICO` are two different polynomial
systems for the same primitive; a new objective tag for LowMC, whose key recovery is neither
`CicoExact` nor `MqRoot`; and one field the registry does not yet have anywhere — the **published
competitor figure**, which `ExternalStatus` cannot carry because it records whether and when a
problem was solved elsewhere and not at what cost.

`tools/check-griffin-reconstruction.py` is that survey's one executable result. It instantiates
Griffin with `(t, α) = (12, 3)` over the 55-bit prime `p = 28407454060060787` from the constants
published in the FreeLunch appendix, and reproduces all five published CICO solutions for
`r ∈ {5, 6, 7}`:

```sh
tools/check-griffin-reconstruction.py            # 43 ms, standard library only
tools/check-griffin-reconstruction.py --verbose  # print each reconstructed output
```

It exists because the specification is *not* complete on its own: the linear layer comes from the
designers' reference implementation, and the paper's `(δ, µ)` index convention is ambiguous. The
published witnesses decide the ambiguity — one reading reproduces 5 of 5 and the other 0 of 5 — so
the instance is reconstructed rather than guessed. That is the argument the document makes for
preferring candidates that publish a witness.

### Courtois MinRank A–F, where the challenge is a parameter set and not a file

[`docs/research/minrank.md`](../research/minrank.md) is the provenance record for the six MinRank
challenges Courtois proposed in 2001, read from the original publication rather than from the
literature that cites it. The parameters are verified and are committed, machine-readable, in
`research/minrank/courtois-challenges.tsv`; `tests/minrank_challenges.rs` re-derives the paper's own
solution-probability column from them, so a transcription slip in any of `q`, `η`, `n`, `m` or `r`
fails a test instead of propagating.

The finding that matters is negative. The paper proposes "six **sets of parameters** A-F"; it
publishes no matrices, offers no prize, and the scheme's official page — archived eight times
between 2001 and 2003 — carries papers and slides only. **No authentic instance of any of A–F was
ever published**, and the construction that would regenerate one needs a 160-bit seed and a
generator the paper names neither of. Every published break ran on an instance its authors generated — the only
executed solve of C, Steel's of 23 August 2014, on "a random instance over `GF(65521)`", and the
2026 one on D, whose abstract says so in as many words ("**an** instance"); the 2010 result on C is
a method and a projection, not a completed run. So a same-parameter instance here is not a degraded substitute — it is the same kind of
object every published result used — but the published costs stay a **difficulty scale and not a
comparand**, and nothing is in [the registry](#the-challenge-registry) until a generator exists to
digest. The document also corrects the verifier: the condition is `rank(Σ αᵢ Mᵢ − M₀) ≤ r` over
`1 + m` matrices, so challenge A is eleven `6 × 6` matrices over `GF(65521)`, not ten.

### Anemoi, the first candidate actually imported

`grobner::research::anemoi` is the permutation half of candidate 1: Anemoi at `ℓ = 1` over
`p = 2^64 − 353`, `α = 3`, transcribed from the designers' reference implementation (MIT,
`3e86ff0c`) and the CRYPTO 2023 paper. The round constants are **derived, not tabulated** — they
come out of the first two hundred digits of π — and the modulus is odd, so
`Zp18446744073709551263` holds it in Montgomery form with no new field arithmetic.

```rust
use zeebra::{
    fields::Zp18446744073709551263,
    grobner::research::{Anemoi, AnemoiParameters},
    FiniteField,
};

let anemoi = Anemoi::<Zp18446744073709551263>::new(AnemoiParameters::six_worlds(4)).unwrap();
assert!(anemoi.is_cico_solution(Zp18446744073709551263::new(8251407552160637060)));
```

The one choice the paper leaves open is `g`, "a generator of the multiplicative subgroup"; the
reference takes Sage's smallest primitive root, which is `g = 5` here. That is a **convention rather
than a specification**, so `smallest_primitive_root` reproduces the convention and
`Anemoi::derived_digest` pins what it produced — a parameter checksum covers `p`, `α`, `ℓ` and `N`
and would not notice a changed generator moving every constant.

Verification does not rely on the transcription being read correctly. The Six Worlds logs
(<https://github.com/IAIK/six-worlds-anemoi>, MIT `fa056e6f`) print complete lexicographic Gröbner
bases, and four CICO witnesses were extracted from them by rooting the lex univariate and reading
each root back into the permutation's own input coordinates. The witness **count** matches the logs'
own `nsols` line at every rung — 2, 1, 0 and 1 at `N = 1, 2, 3, 4` — including the rung with no
solution. [`docs/research/anemoi.md`](../research/anemoi.md) records every source URL, the
ideal-membership check that needs no roots, and one trap: the logs' variable labels are positionally
permuted relative to the model's own names, and the two orders coincide at `N = 1`.

Ten rows are registered — `N = 1 … 5` in both published models — and frozen by
`test_the_registry_is_frozen` **before** anything is run. Two registry changes were needed:

- **`ChallengeParameters::AnemoiCico` carries the algebraic model, so the model is inside the
  identity digest.** `FCICO` at `N = 5` is ten generators of degree three; `PCICO` is six of degrees
  up to ten. Same primitive, same solutions, two systems a solver meets completely differently — so
  without the model in `canonical_lines` the two digests would collide and a comparison tool keyed
  on the digest would compare them.
- **`ReferencePoint` is where a published competitor figure lives.** `ExternalStatus` records
  *whether and when* a problem was solved elsewhere and carries no time, no memory and no hardware,
  so "22 057 s of FGLM at `N = 5` on an Intel Xeon E5-2630 v3 under Magma V2.26-2" had nowhere to
  go. It sits **outside** `canonical()`, for the same reason a bounty does: a corrected
  extrapolation must not change what a problem *is*. The basis step and the conversion step are
  separate points — the finding is that they are 2 400x apart — and `reported_memory` is `None` on
  every row, because the logs report peak resident once per sweep and not per row.

The class is `Official` rather than `FaithfulReduction`: the registered object *is* the published
object — Six Worlds ran those round counts and reported them as its own experiment — and there is no
registered full-round Anemoi for a reduction to name. `ExternalStatus::PublishedWithAnswer` then
makes a verified witness a `Reproduction`, which is the strongest honest claim on a solved reduced
instance. The caveat a reduction would have carried structurally is in each row's notes: a result at
`N = 5` says nothing about full-round Anemoi, which is 21 rounds.

#### The machine-independent check, which is read first

`dim F_p[x]/I` does not depend on the machine, the library or the wall clock, so it is the one
number zeebra can be right or wrong about with no reference to a clock — and a disagreement is a
**defect in zeebra or in the model, not a performance difference**. The published value is
`(α+2)^N`, and zeebra's own figure agrees at **all ten registered rows**, both models, `N = 1 … 5`:
5, 25, 125, 625, 3125.

```sh
cargo run --release --example anemoi_ladder list        # the ten rows and their published figures
cargo run --release --example anemoi_ladder dimensions  # the gate; pins no environment, needs none
ZEEBRA_MACHINE=... ZEEBRA_AFFINITY=... tools/benchlock.sh \
    cargo run --release --example anemoi_ladder row anemoi64-cico-n3-fcico
```

`row` runs F4, then FGLM, then root finding, each timed separately — separately because the
published finding is that the conversion costs 2 400x the basis at `N = 5`, and a combined figure
would hide it — and checks any recovered point **through the permutation** rather than through the
system that produced it. At `N = 1` it lands on `8431162935045355170`, which is the witness the
reference's own lex basis determines: zeebra reaches a reference point through a different pipeline.

**`row` refuses to print a single number unless `ZEEBRA_MACHINE` and `ZEEBRA_AFFINITY` are set**, and
exits 2 if they are not. An unpinned wall-clock figure is not a measurement, and one produced by
accident is one that gets quoted later; measurements must also be serialized under
`tools/benchlock.sh`. The timed ladder is a follow-up, and `(α+2)^N` is checked at `N = 1 … 4` by a
unit test so a regression fails CI rather than appearing as a table row.

#### `ACICO`, the third model — where the basis is free instead of the conversion

`AnemoiModel::Acico` is Campa and Roy's model of the same permutation (eprint 2025/814,
Definition 14): `2N + 1` equations in `2N + 1` variables at `ℓ = 1`, with the `x` half of the state
substituted by `Q_δ(y) + s^α` rather than carried. That substitution is the whole model, and it is
why no degree compounds — `α, 1, 2α, α, …` at every round count, against `PCICO`'s `3, 4, 6, 8, 10`.

```sh
cargo run --release --example anemoi_acico structure  # Propositions 2 and 4, machine-independent
cargo run --release --example anemoi_acico weighted   # alpha in {5, 7, 11} over WDRL, Proposition 3
cargo run --release --example anemoi_acico shape      # both halves of shape position, labelled
ZEEBRA_MACHINE=... ZEEBRA_AFFINITY=... tools/benchlock.sh \
    cargo run --release --example anemoi_acico cost 4
```

What is reproduced, and each of these is a third-party prediction rather than a self-check: the
**whole leading-monomial set** of the DRL basis, `{y_0} ∪ {y_j^α, s_j^α, y_j s_j}`, at `N = 1 … 6`;
the quotient dimension `(α + 2)^N`, which Proposition 4 **proves** where §5's figure for the other
two models is only observed, so `proved_acico_quotient_dimension` and
`published_quotient_dimension` are two functions with the same arithmetic and different claim
strengths; a solving degree flat in `N`, and in a stronger form than published — the F4 *step-degree
sequence* is identical at every `N ≥ 2`, not just its maximum; and `α ∈ {5, 7, 11}` over the weighted
order #306 introduced, where Proposition 3's different leading monomials `{y_j^2, s_j^{α+1}}` come out
exactly. Faithfulness is checked against the permutation three ways, the strongest being that the
model's last generator **evaluates to `Anemoi(0, y).0` at every input** rather than merely vanishing
at a witness.

The measured point of the model: at `D = 3 125` the basis is **0.00053 s** against `FCICO`'s ≈ 16 s
and `PCICO`'s ≈ 0.8 s, while all three conversions sit within 1.3x of each other. The basis is a
property of the model; the conversion is a property of `D`. `N = 6` reaches `D = 15 625` inside
every default F4 budget, where the other two models needed all four lifted (#323).

[`docs/research/anemoi.md`](../research/anemoi.md) §10 has the figures, the cross-characteristic
caveat on that comparison, and §10.5's reading of why "`ACICO` is the first *proven* shape-position
family" does not survive the proof as printed.

### Feistel-MiMC and Rescue-Prime, the 2021–2022 EF bounty primitives

Two more imported primitives, both over `p = 2^64 − 59` — the fastest non-trivial field in the table
above at 1.71 ns per multiply, and until now the one nothing exercised cryptanalytically.
[`docs/research/mimc-rescue.md`](../research/mimc-rescue.md) is the full account;
[`docs/research/ef-cryptanalysis.md`](../research/ef-cryptanalysis.md) §4 is the survey the
parameters come from.

**The reference ships known-answer tests and all ten reproduce.** `zkfriendlyhashzoo` at
`b9c09d5a6302725a65ff59e4219d1beb4c524154` (MIT) publishes one per instance — five Feistel-MiMC
round counts and five Rescue-Prime instances — and each output depends on every round constant, the
S-box placement and the field, so reproducing all ten is a third-party oracle rather than a self-
check. That is the standard #197 set: two fields of the same order with different moduli are
indistinguishable by any shape check, so only a published vector can tell them apart.

The two primitives make opposite choices about their constants and each module follows its own:

- **Feistel-MiMC derives them**, from a SHAKE128 seeded with `"FeistelMimc"` and the field
  characteristic. `src/util/shake128.rs` is a hand-written Keccak-f[1600] for it, beside the
  existing SHA-256. One detail decides every constant and no shape check could catch it: the
  reference's `ff` repr is **two** limbs wide for a 64-bit modulus, so the seed absorbs `p` followed
  by eight zero bytes, while `KnownOrder::characteristic_limbs()` is canonical and reports one limb.
  `FeistelMimc::derived_digest` pins the result.
- **Rescue-Prime tabulates them**, so they are transcribed into
  `research/rescue-prime/bounty-constants.txt` with the source file's digest in its header. Its
  inverse S-box exponent `α^{-1} mod (p − 1)` is **computed from the field's order**, not copied, and
  a test checks `x^α` and `x^{α^{-1}}` are mutually inverse by evaluation — `12297829382473034371`
  here against Anemoi's `12297829382473034175`, two numbers a glance cannot tell apart.

Both record **`m` is not always 3**: three of the five Rescue-Prime bounty instances are `t = 2`,
against the `m = 3` both #203 and #71 describe. And both Feistel-MiMC ladders are carried, because
the published parameters were revised: `r ∈ {6, 10, 14, 18, 22}` was replaced by
`r ∈ {22, 25, 30, 35, 40}` after `r = 14` and `r = 18` fell to equation solving, so **the old
hardest rung became the new easiest** and "r = 22" is ambiguous without a ladder named beside it.

Feistel-MiMC CICO has **two models that differ in kind**, which is what makes it worth generating
rather than duplicating the Poseidon work. There is no MDS layer, so nothing couples the branches
and the round relation `A_{j+1} = A_{j−1} + (A_j + c_j)^α` is a recurrence in one unknown:
eliminating the intermediates by substitution leaves a **single univariate of degree `α^r`**, which
is root-finding's problem and not F4's. The per-round model is `r` cubics in `r` variables, square
and zero-dimensional with no slice. `test_the_two_formulations_have_the_same_solution_set` asserts
they agree on the whole solution set — the univariate's roots are exhaustive over the base field —
before any cost is compared. The `t = 3` Rescue-Prime instances are **underdetermined by one**
(`N − E = t − 2k`), so they are not comparable to a square rung at matched variable count without a
slice.

Measured, the two findings both run against the expectation:

- **The univariate route wins at every round count measured.** At `r = 7`, root finding costs 957 ms
  against F4's 11 255 ms — 12x — and the eliminant takes 0.9 ms to build. There is a reason rather
  than a horse race: the per-round system is a complete intersection of `r` cubics, so its quotient
  dimension is exactly `α^r` by Bézout, which *is* the univariate's degree. The univariate is the
  smallest possible eliminant, and computing it beats computing the basis that encodes it.
- **Removing the MDS layer moved the frontier in, not out.** Feistel-MiMC fails at nine variables
  where Poseidon `t = 2` succeeds in 371 ms, both square. Variable count is the wrong axis, and the
  quotient dimension says why: in both families it is `α^{rounds}`, the degree of the univariate
  eliminant, *not* the Bézout number `α^{variables}`. A Feistel network introduces one variable per
  round, so nine variables is nine rounds and `3^9 = 19 683`; Poseidon `t = 2` introduces two, so
  nine variables is four rounds and `3^4 = 81`. A factor of **243** in the governing quantity at
  identical variable count. `poseidon.md` §6's "the dense MDS layer is the structural obstacle, not
  the variable count" therefore needs amending — the MDS layer is what makes `t = 3` fail where
  `t = 2` succeeds *at equal width*, not what bounds the frontier in general.

Two rejections are recorded so they are not reopened. **MiMCSponge is not a polynomial-solving
target**: its challenge objective is a *collision*, which is birthday-bounded. **Reinforced Concrete
is not expressible** at any useful degree: its S-box decomposes into digits and inverts each modulo
a different modulus `v`.

`solve_one` is not a convenience wrapper. Time to one solution is dominated by the Gröbner basis
and barely depends on how many solutions exist, while enumerating them all scales with the count —
on a 14-variable system with 16384 solutions that is 1.9 ms against 1.6 s, a factor of **830**.

The older `grobner::solve` is unchanged and still the right call for a positive-dimensional system,
which it handles by enumerating the field.

**Neither strategy dominates.** `SolveStrategy::GrevlexF4ThenFglm` is the only route to katsura-7,
whose lex basis crosses F4's limits; `SolveStrategy::DirectLexF4`, the default, is the only route to
planted-12 and planted-14, whose quotient algebras are too large to build. `cargo run --release
--example solve_one` shows both failures. `solve_one_planned` will choose for you — see
[Letting the solver choose](#letting-the-solver-choose) below — but the choice stays the caller's
by default.

Whether conversion is worth doing depends entirely on the system —
`cargo run --release --example fglm_conversion` measures it. On cyclic-6 the pipeline is **7.4x**
faster than direct lex F4, on katsura-6 **2.5x**, and on katsura-7 direct lex F4 produces **no
basis at all** while the pipeline finishes in 68 ms. On the planted family it loses by up to
**65x**. Automatic selection is opt-in rather than default, and it is not a cost heuristic: it
opens with the route whose *refusal* is cheap and decides the conversion's feasibility from a
counted quotient dimension. See [Letting the solver choose](#letting-the-solver-choose).
