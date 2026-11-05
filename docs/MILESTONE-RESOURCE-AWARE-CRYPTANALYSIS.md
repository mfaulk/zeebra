# Milestone: Resource-Aware Solving and Cryptanalysis Research Infrastructure

**Status:** M21-0 in progress. M20-C landed as a prerequisite (see §2). The baseline of §4 is
measured and committed as `examples/solve_baseline.rs`.
**Prerequisites:** M20 merged, including M20-C's byte-accounted limits.
**Objective:** turn the existing F4/FGLM algorithms into a solving system that chooses a route on
stated grounds, reports what limited it when it fails, and can be evaluated on independently
specified cryptanalytic problems.

## 1. What this milestone is actually blocked on

The plan asks for two things: a resource-aware solver, and a reproducible cryptanalysis experiment
framework. Reading the code first changes the order they should be built in.

> **The solver already distinguishes the mathematical outcomes correctly and already enforces its
> budgets. What it does not do is *report* anything.** `solve_zero_dimensional.rs`'s `lex_basis`
> computes an `F4Statistics` on both routes and discards it with `let (basis, _) = ...`, twice.
> `SolveStatistics` carries no F4 figures at all — not matrix shape, not peak entries, not time.

So a planner built today would be choosing between two routes whose costs it cannot see, and a
failed attempt would tell a caller which limit was crossed but nothing about the work that reached
it. §4's baseline had to re-run the whole pipeline alongside `solve_one_with_options` to get the
numbers in it, and that duplication is the measurement.

This reorders the milestone. **Diagnostics before heuristics**, which is also the plan's own closing
recommendation: a solver that accurately reports why it failed is more useful than one that picks a
strategy without evidence its choices are sound.

### 1.1 Two mathematical outcomes are conflated today

`SolveError`'s doc comment is careful about this and the implementation is one case short:

| mathematical fact | what `solve_one` returns |
|---|---|
| a point exists | `Ok(Some(p))` |
| zero-dimensional, no point over `F` | `Ok(None)` |
| `1 ∈ I` — the system is inconsistent | **`Ok(None)`** |
| not zero-dimensional | `Err(PositiveDimensional)` |
| a budget was crossed | `Err(Grobner(..))` / `Err(Fglm(..))` / … |

The third row is the defect. `search` returns an empty solution list when the basis contains a
nonzero constant, which is correct — an inconsistent system has no solutions — but "there are no
solutions because the equations contradict each other" and "there are no solutions in this field
although the variety is nonempty over an extension" are different answers to a cryptanalytic
question. §6.2 proposes the type that separates them. Note that the fifth row is already correct
and must stay so: **`Ok(None)` is never returned because a budget was crossed**, and §9.4 of the
plan asks only that this be preserved.

### 1.2 Estimated bytes are not measured bytes, by a factor of four

Measured, not asserted. katsura-7 under lex at `F4Options::default()`:

| | |
|---|---:|
| `max_live_nonzeros` crossed at | 20,003,295 entries |
| which `max_live_bytes` accounts as | 320 MB |
| process peak RSS | **1,303 MB** |
| time spent before the refusal | **28.6 s** |

A 4.1x gap, and it is not a defect in the accounting — §5.2 of
`docs/MILESTONE-LARGE-PRIME-FIELDS.md` lists what the entry budget deliberately omits (the
monomial-to-column map, the basis's term vectors, the backend's dense buffer, allocator overhead).
It is the reason M21 must label every memory figure with which of four things it is:

1. **mathematical dimensions** — `max_live_nonzeros`, `quotient_dimension`,
2. **representation entries and cells** — what the entry budgets count,
3. **estimated allocated bytes** — `F4Statistics::peak_live_bytes`, `FglmMemory`,
4. **measured process RSS** — `util::peak_resident_bytes`.

A configured budget is a cooperative limit on (2) stated in (3). It is not a guarantee about (4),
and M21 must not describe it as one.

Two figures to keep apart within (3), because the baseline now prints both. The count in the
*error* is the live count at the crossing — 20,003,295 entries, 320 MB. `max_live_nonzeros` is the
peak of the last elimination that *finished*, which on this instance is 18,148,835 entries and
290 MB. The second is lower by construction: the batch that crossed the budget never completed, so
its peak was never recorded. Neither is wrong; they answer different questions, and a report that
quoted one as the other would overstate or understate by a batch.

### 1.3 Over a wide field, the cost is not in the matrices

Also measured. The same system over GF(2^31 − 1) and over BN254 `Fr`:

| system | field | F4 (grevlex) | whole `solve_one` |
|---|---|---:|---:|
| katsura-5 | GF(2^31−1) | — | — |
| katsura-5 | BN254 `Fr` | 1.0 ms | **42.6 ms** |
| katsura-6 | BN254 `Fr` | 7.1 ms | **172.9 ms** |
| planted-8 | BN254 `Fr` | 0.1 ms | **30.9 ms** |

F4 and the conversion are a few percent of the end-to-end time over BN254, and the rest is the
back-substitution search and its univariate root finding — which is unsurprising once §4.1 of the
large-prime-fields milestone is read: **inversion over BN254 is 202 multiplies**, 3.77 µs. A
planner whose cost model is about matrix growth is modelling the wrong stage over a wide field.
M21-C's structural analysis must not claim otherwise, and M21-I must report the stage breakdown
rather than a single total.

## 2. M20 handoff

M20-C is **complete** and landed before this document: `F4Options::max_live_bytes` and
`FglmOptions::max_span_bytes`, as second budgets beside the entry ones. See §5.2 of
`docs/MILESTONE-LARGE-PRIME-FIELDS.md` for the figures. M21 therefore **does not implement another
F4 memory budget**; it consumes `live_entry_allowance::<F>()` and reports
`peak_live_bytes`/`max_dense_buffer_bytes`.

The boundary with M20-E, which is still outstanding:

| | owns |
|---|---|
| **M20-E** | demonstrating and measuring the *existing* algorithms over the *new field widths* |
| **M21** | importing *external* challenge instances, experiment metadata, and comparing *strategies* |

Concretely: a table of katsura/cyclic/planted timings over BN254 and BLS12-381 is M20-E's. A
Fukuoka MQ instance parsed from its published file, solved, and verified against the source
coefficients is M21's. `examples/solve_baseline.rs` sits on the line and is M21's, because its
purpose is the strategy comparison of §5; its wide-field rows are a by-product and M20-E should not
duplicate them but may extend them.

## 3. Mathematical scope and preconditions

Let `I = <f_1, …, f_m> ⊆ F_q[x_1, …, x_n]`. The two existing routes are

```text
DirectLexF4         I --F4,lex--> G_lex --roots--> points
GrevlexF4ThenFglm   I --F4,grevlex--> G_grevlex --FGLM--> G_lex --roots--> points
```

### 3.1 Preconditions, and when each is knowable

| precondition | needed by | knowable before a Gröbner basis? |
|---|---|---|
| `I` is zero-dimensional | both routes | **no** |
| `D = dim_F R/I` | FGLM's span budget | **no** |
| the staircase's shape | FGLM's operator cost | **no** |
| `n`, `m`, degrees, sparsity | nothing, today | yes |

The second column is the whole difficulty. Zero-dimensionality is decided by `classify_ideal` from
a basis's leading monomials, and `D` by enumerating standard monomials — both *after* F4. Before
F4, a planner knows only the input's shape, and **the number of equations against the number of
variables is not a proof of dimension**: cyclic-4 is 4 equations in 4 variables and is
positive-dimensional (§4, measured). M21-C's structural analysis is therefore diagnostics, never a
dimension claim, and M21-D's planner must be written as two phases with the knowledge boundary
between them explicit.

### 3.2 Underdetermined systems and specialization

Many cryptanalytic systems are underdetermined — a Poseidon CICO instance may fix two outputs and
leave fourteen inputs free — so the unspecialized ideal generally has positive dimension and
**classical FGLM does not apply to it**. M21-E's response is specialization: choose `a_i` for
`i ∈ S` and solve `I_a = I|_{x_i = a_i}`.

Two rules, both load-bearing:

1. Every point recovered from `I_a` must be lifted to a full assignment and checked against **every
   original generator**, not against `I_a` and not against any derived basis.
2. `I_a = <1>` **does not** prove `I = <1>`. A random slice of a positive-dimensional variety can
   be empty over `F_q` while the variety is not. A sequence of empty slices is still not a proof.
   Each specialization is an experiment with a recorded seed, and that is all it is.

### 3.3 No implicit field equations

`x_i^q − x_i` is not added to force a finite quotient. It is mathematically correct for base-field
points and its degree is `q`, which is 2^254 for the fields M20 added. Where field equations are
wanted they are an explicit property of an instance manifest, never a default.

## 4. Baseline

`cargo run --release --example solve_baseline`. `F4Options::default()` and `FglmOptions::default()`
throughout; `peak nz` is live matrix entries, `peak MB` those entries estimated in megabytes,
`fill` the worst fill-in ratio over all batches. `solve ms` is the whole of
`solve_one_with_options`, which recomputes the Gröbner stage, so the two time columns are **not**
additive — itself a consequence of §1.

### 4.1 GF(2^31 − 1)

| system | route | f4 ms | max matrix | peak nz | peak MB | conversion | solve ms | outcome |
|---|---|---:|---:|---:|---:|---|---:|---|
| katsura-6 | direct | 19.7 | 92x169 | 5,623 | 0.1 | — | 20.8 | verified point |
| katsura-6 | fglm | 3.0 | 431x458 | 6,014 | 0.1 | D=32, 0.1 MB | **6.0** | verified point |
| katsura-7 | direct | — | 7320x33792 | 18,148,835 | 290.4 | — | **28,258** | **F4 entry budget crossed** |
| katsura-7 | fglm | 29.8 | 1262x1320 | 27,356 | 0.4 | D=64, 0.2 MB | **47.5** | verified point |
| cyclic-5 | direct | 2.3 | 161x185 | 2,243 | 0.0 | — | 2.6 | no F-point |
| cyclic-5 | fglm | 1.3 | 111x115 | 1,206 | 0.0 | D=70, 0.1 MB | 2.1 | no F-point |
| cyclic-6 | direct | 297.5 | 5135x5158 | 235,317 | 3.8 | — | 296.7 | no F-point |
| cyclic-6 | fglm | 11.7 | 386x391 | 9,046 | 0.1 | D=156, 0.7 MB | **17.3** | no F-point |
| planted-8 | direct | 0.1 | 20x21 | 53 | 0.0 | — | **0.9** | verified point |
| planted-8 | fglm | 0.0 | 16x17 | 40 | 0.0 | D=256, 1.4 MB | 3.0 | verified point |
| planted-10 | direct | 0.1 | 25x26 | 66 | 0.0 | — | **1.2** | verified point |
| planted-10 | fglm | 0.1 | 20x21 | 50 | 0.0 | D=1024, 21.4 MB | 22.3 | verified point |
| planted-12 | direct | 0.1 | 30x31 | 79 | 0.0 | — | **1.3** | verified point |
| planted-12 | fglm | 0.1 | 24x25 | 60 | 0.0 | **span budget crossed** | 36.0 | **FGLM budget crossed** |
| cyclic-4 | direct | 0.1 | 13x21 | 59 | 0.0 | — | 0.1 | positive-dim |
| cyclic-4 | fglm | 0.1 | 20x25 | 93 | 0.0 | — | 0.1 | positive-dim |

The katsura-7 and cyclic-4 figures above come from `solve_one_reported`, which M21-C added for
exactly this: when the baseline was first written those rows printed `—` across the board, because
a failed attempt dropped every counter and made a 28-second refusal look free. See §6.4.
| inconsistent | direct | 0.0 | 2x2 | 4 | 0.0 | — | 0.0 | inconsistent |
| inconsistent | fglm | 0.0 | 2x2 | 4 | 0.0 | D=0 | 0.0 | inconsistent |
| no-F-point | direct | 0.0 | 0x0 | 0 | 0.0 | — | 0.0 | no F-point |
| no-F-point | fglm | 0.0 | 0x0 | 0 | 0.0 | D=2 | 0.0 | no F-point |

`inconsistent` is `{x − 1, x − 2}`. `no-F-point` is `{x^2 − c, y}` for the smallest `c` that is not
a square in the field, **found by search rather than assumed**: `x^2 + 1` is the obvious choice
over GF(2^31 − 1), which is 3 mod 4, and is *solvable* over BN254 `Fr`, which is 1 mod 4. The first
draft of this baseline used it over both fields and reported a verified point where it meant to
report none. A corpus entry whose outcome class silently depends on the field is worse than no
entry.

### 4.2 BN254 `Fr`, where tractable

| system | route | f4 ms | peak nz | peak MB | conversion | solve ms | outcome |
|---|---|---:|---:|---:|---|---:|---|
| katsura-5 | direct | 1.4 | 532 | 0.0 | — | 42.6 | verified point |
| katsura-5 | fglm | 1.0 | 1,259 | 0.1 | D=16 | 42.6 | verified point |
| katsura-6 | direct | 26.9 | 5,623 | 0.2 | — | 185.0 | verified point |
| katsura-6 | fglm | 7.1 | 6,014 | 0.2 | D=32, 0.2 MB | 172.9 | verified point |
| planted-8 | direct | 0.1 | 53 | 0.0 | — | 24.1 | verified point |
| planted-8 | fglm | 0.1 | 40 | 0.0 | D=256, 5.4 MB | 30.9 | verified point |
| no-F-point | direct | 0.0 | 0 | 0.0 | — | 0.1 | no F-point |
| no-F-point | fglm | 0.0 | 0 | 0.0 | D=2 | 0.1 | no F-point |

The entry counts are *identical* to GF(2^31 − 1)'s on every shared system and the byte figures are
2.5x — which is M20-C's premise, confirmed end to end rather than in a unit test. The `solve ms`
column is §1.3.

### 4.3 The policy conclusion the baseline forces

The two routes crisscross exactly as the plan expects, and the plan's demonstration targets are
reachable: katsura-7 is solvable **only** by conversion, planted-12 **only** directly. But the
baseline says something the plan does not, and it is the most important thing in this document:

> **Failure is not symmetrically priced.** katsura-7's direct attempt burns **28.3 seconds** and
> 1.3 GB before refusing. planted-12's conversion attempt refuses after **36 ms**. A fallback
> policy that tries direct first and converts on failure costs 28.3 s on katsura-7; one that
> converts first and falls back to direct costs 37 ms on planted-12 and 47 ms on katsura-7.
> **Grevlex-first is better by 600x in the worst case on this corpus.**

And the reason is structural rather than incidental, which is what makes it worth building a policy
on. FGLM's binding budget — the span's `2D² + D(D+1)/2` dense cells — is computed from `D` and
checked **before anything is allocated**, so a refusal costs one quotient-basis enumeration. F4's
binding budget is discovered *during* elimination, after every row operation, so a refusal costs
the whole elimination up to the crossing. One route can say "no" cheaply by construction and the
other cannot.

Note what this contradicts. `SolveStrategy::DirectLexF4` is the current `#[default]`, and its doc
comment says it is "the conservative choice". On this corpus and under automatic fallback it is the
*expensive* choice, because the conservative question is not "which route usually wins" but "which
route's failure is affordable". §5 builds the policy on that. **M21-I must re-measure it**: ten
systems from two synthetic families and three degenerate cases are not evidence about cryptographic
instances, and the ordering could invert on a system whose grevlex basis is itself out of reach.

Three smaller results, recorded so they are not rediscovered:

- Conversion is faster than direct on **every** katsura and cyclic row here (3.5x on katsura-6,
  17x on cyclic-6) and slower on **every** planted row. The planted family's quotient dimension is
  `4^(n/2)`, so FGLM's cost is exponential in `n` where its lex basis stays trivial.
- cyclic-4 is refused as positive-dimensional by both routes at 0.1 ms, from the first basis
  computed. The cheap case is genuinely cheap, and no planner needs a heuristic for it.
- The `no-F-point` and `inconsistent` rows cost nothing and reach the right mathematical answer by
  both routes — except that the solver cannot report which of the two it reached (§1.1).

## 5. Strategy selection policy

### 5.1 What stays

`SolveStrategy`'s two variants, and the exact semantics of `solve_one`,
`solve_one_with_options`, `solve_zero_dimensional` and `solve_zero_dimensional_with_options`.
Nothing automatic is added to them. The policy layer is new surface, opted into.

### 5.2 The policy

```rust
pub enum SolvePolicy {
    /// Exactly what is asked for. The only behaviour that exists today.
    Explicit(SolveStrategy),

    /// One route, chosen on stated grounds. No second attempt.
    ConservativeAuto,

    /// As above, with one alternative attempt permitted from a shared budget.
    AutoWithFallback,
}
```

`ConservativeAuto`'s rules, in order, each annotated with what it is allowed to know:

1. **Structural analysis** (§6.1), cheap and non-committal. If a generator is a nonzero constant,
   report `Inconsistent` without computing anything. This is the only conclusion the input's shape
   licenses.
2. **Compute the grevlex basis.** Chosen by §4.3: its budget refuses cheaply, and it is also the
   faster basis on every corpus system where both complete. *Not* chosen by a cost model — there
   is no evidence for one, and §4.3's reasoning is about the price of being wrong.
3. **Classify.** `classify_ideal` on the grevlex basis. Positive-dimensional ⇒ report it; this
   route does not apply and no budget was at fault.
4. **Enumerate the quotient basis** to get `D`, and compute FGLM's span and operator estimates from
   it. These are facts now, not predictions.
5. **If the estimates fit the remaining budget, convert.** Otherwise the conversion is *known* to
   be infeasible — a computed `D` against a configured budget, not a guess — and under
   `AutoWithFallback` the direct lex route is attempted instead.
6. **If a route crosses a budget**, record the work spent and attempt the alternative only if the
   shared budget still permits it.

Step 5 is where the planner earns its keep: it is the one decision made on a *measured* quantity
rather than an estimate, and it is exactly the decision planted-12 needs.

### 5.3 Budget semantics

Budgets are **shared across attempts**, not per attempt. §4.3 is the argument: a per-attempt budget
lets a fallback spend 28 s and then 47 ms and report the 47 ms, which misrepresents the cost of the
policy rather than of the algorithm. The plan is explicit that a fallback must not silently reset a
caller's budget, and a shared budget is the only arrangement that cannot.

Consequences to implement and test:

- A report states total work across attempts, including discarded work. The successful attempt's
  cost is a component, never the headline.
- The number of attempts is bounded at two. There are only two routes.
- **No resumption is claimed.** F4 cannot continue an abandoned computation under a different
  monomial order, and nothing in M21 will pretend it can. A fallback restarts, and the report says
  so.

### 5.4 Outcome semantics, preserved

`Ok(None)` — or its typed successor in §6.2 — is returned **only** when the computation finished
and established that no base-field point exists. A crossed budget is always an error. This holds
today and M21's tests must pin it, because a planner that retries is exactly the kind of code that
would turn an exhausted attempt into an apparent answer.

## 6. Public API proposals

### 6.1 Structural analysis (M21-C)

```rust
pub struct SystemShape {
    pub variables: usize,
    pub generators: usize,
    pub terms: usize,
    pub max_degree: u64,
    pub degree_histogram: Vec<(u64, usize)>,
    pub occurrences: Vec<usize>,     // per variable
    pub linear_generators: usize,
    pub quadratic_generators: usize,
    pub univariate_generators: usize,
    pub constant_contradiction: bool,
    pub specialization_candidates: Vec<usize>,
}

pub fn analyze<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
) -> SystemShape;
```

Diagnostics. The doc comment must say, and the tests must pin, that **nothing here bounds the
quotient dimension or the solving degree**, with cyclic-4 as the committed counterexample to
`generators == variables ⇒ zero-dimensional`.

### 6.2 Typed outcomes (M21-C)

```rust
pub enum SolveOutcome<const N: usize, F: FiniteField> {
    /// A point, verified against the original generators before it is returned.
    Point([F; N]),
    /// Zero-dimensional, and no point over `F`. An answer.
    NoBaseFieldPoint,
    /// `1 ∈ I`. A different answer.
    Inconsistent,
}
```

`solve_one` keeps returning `Option<[F; N]>`; the new entry point returns this. §1.1 is the defect
it closes.

### 6.3 Failure-aware F4 (M21-C)

The plan sketches an `F4RunReport` and warns against duplicating `F4Statistics`. It need not be
duplicated at all — the accumulator already exists inside `f4_observed` and is simply dropped on
the error path:

```rust
/// As `f4_with_options`, returning the statistics accumulated even when a limit is crossed.
///
/// The basis is inside the `Result`, so a crossed budget cannot be mistaken for a finished one.
pub fn f4_reported<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> (Result<Vec<MultivariatePolynomial<N, F>>, F4Error>, F4Statistics);
```

`f4` and `f4_with_options` are untouched. The partial-basis hazard the plan names is structurally
impossible here: the basis and the error occupy the same `Result`, so there is no value to hand
back that could look complete.

### 6.4 Solver diagnostics (M21-C)

```rust
pub struct SolveStatistics {
    // ... existing fields ...
    /// `1` is in the ideal — which `Ok(None)` could not say.
    pub inconsistent: bool,
    /// What the Gröbner stage cost. `None` only if it was never reached.
    pub f4: Option<F4Statistics>,
    pub fglm: Option<FglmStatistics>,   // existing
}
```

**One thing the plan did not call for, which the baseline made necessary.** Carrying the
statistics on the *success* path is not enough: `solve_one_with_outcome` returns
`Result<(SolveOutcome, SolveStatistics), SolveError>`, so a failed attempt drops every counter —
and a failed attempt is where they matter. Three failures have three different amounts of completed
work behind them:

| failure | completed work behind it |
|---|---|
| `PositiveDimensional` | a **complete** Gröbner basis |
| conversion crossed its budget | a complete **source** basis |
| F4 crossed its budget | no basis, but the batches it managed |

In the first baseline every one of those printed `—` for matrix shape and `0.0` for bytes, which
made cyclic-4's refusal and planted-12's look free. So M21-C adds the one-level-up analogue of
§6.3:

```rust
pub fn solve_one_reported<const N: usize, F: KnownOrder, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
    options: &SolveOptions,
) -> (Result<SolveOutcome<N, F>, SolveError>, SolveStatistics);
```

A tuple rather than statistics inside `SolveError`, for the reason §6.3 gives: the error is `Copy`,
every caller matches it exhaustively, and work inside a failure conflates the two. M21-D needs this
— a policy that cannot see what a discarded attempt spent cannot charge a shared budget for it.

### 6.5 Specialization (M21-E)

```rust
pub struct Specialization<const N: usize, F: FiniteField> {
    pub fixed: Vec<(usize, F)>,
    pub seed: Option<u64>,
}

pub fn specialize<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    specialization: &Specialization<N, F>,
) -> Vec<MultivariatePolynomial<N, F>>;

pub fn lift<const N: usize, F: FiniteField>(
    specialization: &Specialization<N, F>,
    partial: &[F; N],
) -> [F; N];
```

Specialized variables stay as inactive positions in the same `N`-variable ring. `const N` is not
replaced, and no second polynomial representation is introduced.

### 6.6 Instance dimensions (M21-A)

`MultivariatePolynomial<const N: usize, F>` means a runtime variable count cannot be dispatched
generically. M21-A supports a documented finite set of `N` by explicit dispatch, and an unsupported
dimension is a clear error rather than a panic. The type system is not redesigned.

## 7. Experiment schema and corpus

### 7.1 Instance manifests (M21-A, issue #73)

Input definitions are separated from measured results, so that a new workstation's timings do not
change an instance. A manifest carries: identifier; source and source version; repository URL and
commit; field characteristic, extension degree, and modulus or irreducible polynomial; variable
count, names, and order; generators or their deterministic construction; monomial-order
conventions; the mathematical objective; any known witness; the independent verification method;
expected quotient dimension where known, labelled **proved** or **observed**; a dataset checksum;
and redistribution terms.

### 7.2 Corpus

| category | instances | purpose |
|---|---|---|
| classical algebra | §4's ten entries | regression, and the strategy comparison |
| public MQ | small Fukuoka GF(31) instances (#70) | external reproducibility |
| cryptographic | reduced-round Poseidon (#71, #78) | real structure, independent verification |

GF(31) needs no new arithmetic: `PrimeFieldElement64<31>` exists. KoalaBear is
`PrimeFieldElement64<2130706433>`. A compact 32-bit representation is issue #62 and an independent
optimization. GF(2^8) needs the binary and extension field modules exported, which is deliberate
scope and must not be smuggled into the first importer PR.

### 7.3 Validation requirements

- Imported MQ coefficients are checked against the source file by independent evaluation, which is
  what catches a monomial-order translation error.
- Poseidon equations are checked by substituting intermediate states from a pinned reference
  implementation and asserting every equation is zero, **and** by corrupting selected states and
  asserting the expected equations fail.
- Every recovered witness passes the external verifier, not only zeebra's polynomial evaluator.
- The official verifier's relaxed low-bit conditions are **not** modelled as field equalities. A
  condition on the low bits of a canonical integer representative is not a polynomial equation over
  the field, and the exact reduced-round constraints are what the Gröbner experiments use.
- No full-round security claim is inferred from a reduced-round experiment.

## 8. Sub-milestones

Parent tracking issue: #90.

| ID | Deliverable | Issue | Depends on |
|---|---|---|---|
| **M21-0** | This document, the M20-C handoff, and §4's baseline | #91 | M20-C |
| **M21-A** | Instance manifests and the Fukuoka MQ importer | #92 | M21-0 |
| **M21-B** | Faithful reduced-round Poseidon generation and external verification | #93 | M21-0 |
| **M21-C** | Structural analysis, typed outcomes, failure-aware diagnostics | #94 | M21-0 |
| **M21-D** | Automatic planning and bounded fallback | #95 | M21-C |
| **M21-E** | Specialization of underdetermined systems | #96 | M21-A/M21-B interfaces |
| **M21-I** | Integrated experiments, comparison, milestone report | #97 | all |

M21-A, M21-B and M21-C are independent and suitable for separate worktrees. M21-D must not start
before M21-C, for the reason in §1. Concurrent work on `SolveOptions`, `SolveError` or the F4/FGLM
option types should be avoided; M21-C owns them for the duration.

## 9. Acceptance criteria

### M21-0

- [x] The merged solver surface reviewed — `solve_one`, `solve_zero_dimensional`, `SolveOptions`,
      `SolveStrategy`, `F4Options`, `F4Statistics`, `FglmOptions`, `FglmStatistics`,
      `QuotientBasis`, `classify_ideal`, and the differential harness
- [x] M20-C closed out first, so M21 consumes byte-accounted limits rather than adding another
      budget (§2)
- [x] The M20-E boundary stated (§2)
- [x] Baseline measured over both routes on katsura-6/7, cyclic-5/6, planted-8/10/12, a
      positive-dimensional system, an inconsistent system, and a zero-dimensional system with no
      base-field point (§4.1)
- [x] Baseline extended to a wide field on the tractable cases (§4.2)
- [x] Baseline committed as a reproducible example, not pasted numbers
- [x] Strategy selection policy specified, with its evidence (§4.3, §5)
- [x] Resource and failure semantics specified, including the four quantities of §1.2 and the
      shared-budget rule of §5.3
- [x] Experiment schema and corpus specified (§7)
- [x] Validation requirements specified (§7.3)
- [x] Public API proposals stated (§6)
- [ ] Architecture approved — the exit criterion (#91)

### M21-C

- [x] `analyze` reports the shape of §6.1 without computing a Gröbner basis
- [x] A test pins that no structural figure is treated as a dimension claim, with cyclic-4 as the
      committed counterexample — it and katsura-4 agree on every reported column and differ in
      dimension
- [x] `SolveOutcome` distinguishes `NoBaseFieldPoint` from `Inconsistent`, with both reachable and
      both tested, under both routes
- [x] `f4_reported` returns accumulated statistics on the error path; `f4` and `f4_with_options`
      are unchanged, and the two paths are asserted to agree where both succeed
- [x] `SolveStatistics` carries the Gröbner stage's `F4Statistics`, so `examples/solve_baseline.rs`
      no longer re-runs the pipeline
- [x] A **failed** attempt keeps its diagnostics too, through `solve_one_reported` — see §6.4 for
      why this was added beyond the plan
- [x] Estimated bytes and measured RSS are reported as separate, differently labelled quantities;
      `estimated_peak_bytes` is the max of the two stage estimates and not their sum, because F4's
      matrices are gone before the conversion allocates
- [x] A crossed budget never produces a no-solution answer — tested across six budgets on a system
      that does have a point, so a wrong answer would fail rather than a missing one

### M21-D

- [ ] `SolvePolicy` is opt-in; explicit strategy behaviour is bit-for-bit unchanged
- [ ] Every attempt is recorded with the reason it was chosen and the work it spent, including
      discarded work
- [ ] Budgets are shared across attempts and a fallback cannot reset them
- [ ] katsura-7 and planted-12 both succeed under one policy and one budget configuration, with no
      input-specific special-casing and no benchmark names in the planner
- [ ] cyclic-4 is reported positive-dimensional, not sent through FGLM
- [ ] An inconsistent ideal, and a zero-dimensional ideal with no base-field point, each reach the
      correct distinct outcome
- [ ] A system on which every permitted route exhausts its budget reports inconclusive
- [ ] The fallback order of §4.3 is re-measured, and the policy's order follows the measurement
      rather than this document

### M21-E

- [ ] Substitution is correct on hand-derived examples
- [ ] Every reported witness satisfies every original generator after lifting
- [ ] Seeds, fixed variables, and assigned values are recorded and reproducible
- [ ] An empty specialization is reported as an experiment, never as unsatisfiability of the
      original system — tested with a system that is satisfiable and a slice that is not

## 10. Risks

**The planner's route order is wrong on real instances.** §4.3's ordering rests on ten synthetic
systems. Mitigation: the order is a documented policy with its evidence attached, explicit selection
is preserved, and M21-I re-measures before the order is called settled.

**Dimension cannot be known before a basis.** Mitigation: §5.2's steps are annotated with what each
may know, and §6.1's analysis is typed and documented as diagnostics.

**Fallback doubles the cost.** Mitigation: shared budgets, two attempts maximum, discarded work
reported (§5.3).

**A byte budget is mistaken for a memory guarantee.** It is off by 4.1x on katsura-7 (§1.2).
Mitigation: the four quantities are named separately everywhere, and the one measured figure is
labelled as such.

**The framework becomes an application.** Mitigation: two external families and a small versioned
manifest first; a CLI only after the library interfaces hold still.

**Scope drifts into new algorithms.** HDF4, mutant F4, crossbred, XL, block Wiedemann, resultants
and Graeffe transforms are out. M21 measures whether they are needed; issues #74–#76 and #82–#85
hold the work.

## 11. Definition of done

Zeebra can load a publicly specified instance, validate it against its source and field spec,
analyze its observable structure, choose a route under a stated policy and a shared budget, run it,
record the work including what was discarded, decide from a computed `D` whether conversion is
feasible, attempt the alternative when the policy permits, extract a candidate point, verify it
against the original system and an independent verifier, and emit a reproducible report. For
underdetermined systems the same flow records its specialization and verifies the lifted solution.

The milestone succeeds when zeebra can say not just whether an experiment succeeded, but **what was
attempted, why it was chosen, what limited it, and whether the result is independently correct.**
