# Proposal: a ZDD equivalence checker over structured Boolean circuits (#1211)

**Status:** proposal, 2026-11-27. **Not accepted.** The owner decides whether to accept it. No code
is written until then, and acceptance authorizes only the bounded prototype and measurement in §8.
**Measured at:** not measured here. Every figure below is quoted from #1168's note, which was measured
at `2eb16995` on a laptop as development figures. This proposal takes no measurements of its own. The
figures that decide it are the bench-host figures §7 predeclares.

Parent: #196. Follows: #1168 ([`boolean-zdd-normal-forms.md`](boolean-zdd-normal-forms.md),
disposition GO, qualified). Non-goals shared with #1156 ([`gf2-point-solving.md`](gf2-point-solving.md)).

## 0. Summary

| | |
|---|---|
| consumer | **combinational equivalence checking** of two circuits that share their inputs, written as triangular rules over `GF(2)` |
| output contract | exactly one of three: **`Equivalent`** (a decided zero), **`Differ`** (a point, independently re-checked), or a **typed refusal**. Nothing partial is returned, and no diagram leaves the manager (§2) |
| why this consumer | its normal form is `0` or a single input assignment, so #1168's 10^3–10^4× gain is never spent converting the result to ANF. That conversion is what reduced the gain to 2–4× (R_out) |
| GC | mark-and-sweep at safe points between signals, with a free list, node ids that never move, and a full cache purge. Roots are the live frontier of a bottom-up sweep (§4). Reference counting is costed and rejected |
| deciding gates | G1 against the expanded-ANF route (R ≥ 10, lower 95% bound, on 2 of 3 structured families, natural and scrambled orders); G2 against kissat 4.0.4 on the miter CNF; G3 the GC's cost and effect; G4 correctness; G5 fail-safe behaviour on dense MQ (§7) |
| unchanged | `Monomial`, every `GF(2)` field type, every default, `src/grobner`, `src/linalg`, `src/fields`. The work stays behind `research-zdd` (§9) |

## 1. Why a consumer, and why this one

#1168 left two qualifiers that any consumer has to answer.

1. **The gain is in the representation of the result.** On adder and ladder, the expanded-ANF
   route's peak intermediate is the size of its output. Ladder's peak terms equal its result terms
   exactly. The canonical ZDD of that output has 55–79 nodes, so a consumer that keeps the diagram
   sees 10^3–10^4×. A consumer that converts the result to ANF pays for the enumeration and sees
   2–4× (`R_out`, #1168 §6). A consumer is worth proposing only if it **never enumerates the
   result**.
2. **Garbage.** On chi8 the prototype allocates 23,838 nodes while its results hold about 420, and
   its state is 2.7 MiB against a 30 KiB ANF bound. A backend needs collection (§4).

Equivalence checking fits (1) by construction. Let circuits A and B share inputs `X`, and let every
other variable be the head of exactly one rule. The rules and the field equations then form a lex
Boolean Gröbner basis (Dagstuhl 10271, Thm. 3.1, as #1168 §1 cites it). Every normal form is a
square-free polynomial in `X` alone, because no head survives reduction. Square-free polynomials in
`X` correspond one to one with Boolean functions of `X`, since ANF is unique. So:

- `NF(u)` is the ANF of the function output `u` computes, and
- outputs `u` of A and `v` of B are equivalent **exactly when `NF(u) = NF(v)`**. In a canonical
  manager that is one comparison of root ids. Equivalently, `NF(u + v) = 0`, the miter form
  Dagstuhl 10271 §4.3 describes, as #1168 §7 cites it.

The result is a bit, or a point when the bit is "differ". The ANF of `NF(u)` is never built.

Other consumers were considered and not chosen:

| candidate | why not first |
|---|---|
| hand the ZDD out (contract A, §2) | no consumer in the crate takes a diagram. It would put GC roots and manager lifetimes into the public API, and the next step any caller takes is `to_anf`, which is the 2–4× route |
| ideal membership for general Boolean systems | needs a Boolean Gröbner basis, not triangular rules. That is the PolyBoRi backend #1168 declined to build, and it changes what `Monomial` means |
| counting points (`#SAT` on the diagram) | the ZDD here is the ANF diagram, not a BDD of the characteristic function. Counting the ones of an ANF needs a transform the prototype does not have. This is a different proposal |
| point solving | #1156 owns it (Gray code, crossbred). A non-goal here |

## 2. Output contracts

#1168's acceptance names three contracts: a ZDD, a verified zero, or a point. They are different
contracts and are kept apart.

| contract | what the caller gets | guarantee | adopted? |
|---|---|---|---|
| **A: ZDD** | a handle to the canonical diagram of `NF(f)` | canonical, exact | **no**: reasons in §1. It stays possible later, and §4's design does not preclude it |
| **B: verified zero** | `Equivalent` | **decided**: exact algebra under checked preconditions, cross-checked by simulation. It is **not** independently certified (below) | **yes** |
| **C: point** | `Differ { pair, inputs }` | **certified**: the assignment is re-evaluated through the original rules by code independent of the manager | **yes** |

B and C are two outcomes of one call, and the call returns one of them or a typed refusal.

### 2.1 Input

```text
Miter {
    vars:    u32,                    // variables 0..vars, no 256 cap (see below)
    inputs:  Vec<u32>,               // the shared inputs X
    rules:   Vec<SparseRule>,        // both circuits' rules, heads disjoint
    pairs:   Vec<(u32, u32)>,        // output pairs (u_k of A, v_k of B), each a head or an input
    order:   VariableOrder,          // level 0 at the top, as in #1168
}
SparseRule { head: u32, tail: Vec<Vec<u32>> }   // square-free monomials, each a sorted var list
```

The prototype's `Anf` is a 256-bit mask (`anf::MAX_VARS = 256`), and `VariableOrder::new` refuses
more than 256 variables. A ripple-carry adder against a Kogge–Stone adder has about
`7n + 2n·log2 n` variables, which passes 256 just above n = 16. That is far below the sizes G2 needs and at
the edge of where route A's term budget would bind. The consumer therefore takes **sparse tails**
and lifts the cap for its own order type. **Route A gets the same sparse terms** (sorted variable
vectors in a hash set), so that its ladder ends at its term budget, as in #1168, and not at a width
cap that would make Z win by default. The bitmask `Anf` stays the test oracle. None of this touches
`Monomial`.

### 2.2 Preconditions, each checked and refused as a typed value

1. The rules are triangular in `order`: distinct heads, every tail variable after its head.
   `TriangularRules::verify` already enforces this, giving `RuleError`.
2. **Coverage.** Every variable is either a declared input or the head of exactly one rule, never
   both. A variable that is neither is refused (`UndefinedSignal`). Otherwise it would act as a free
   input, and `Equivalent` would mean "equivalent for every value of that wire", which is not the
   question asked. A declared input that is also a head is refused (`InputIsHead`).
3. `pairs` is non-empty, and every pair names variables in range.

Under 1–2, the statement in §1 is a theorem. That is what makes contract B a decision rather than a
heuristic.

### 2.3 Output

```text
Ok(Equivalent { pairs: usize, simulated_vectors: usize })
Ok(Differ     { pair: usize, inputs: Vec<bool> })   // inputs indexed like Miter::inputs
Err(EquivalenceError::Rule(RuleError))
Err(EquivalenceError::Shape(..))                    // §2.2 items 2–3
Err(EquivalenceError::Budget(ZddError))             // node or cache budget: nothing partial
Err(EquivalenceError::Internal(..))                 // a self-check failed: a bug, never an answer
```

- **`Equivalent`** means that for every pair `k`, the root of `NF(u_k)` is the root of `NF(v_k)`.
  Its trust rests on the manager being correct. That is why it is a *decided* zero and not a
  certificate. Before it is returned, **S = 1,024 random input vectors** (fixed seed) are simulated
  through both circuits by the bitsliced ANF evaluator, which is independent of the manager. Any
  disagreement is `Internal`. This is a bug detector, not a proof: a nonzero difference of degree
  `d` is caught by one random vector with probability at least `2^-d`.
- **`Differ`** names the first pair, in sweep order (§3), whose roots differ. The witness is built in
  three steps. (i) Form `d = NF(u) + NF(v)`, one XOR. (ii) Walk `d` from its root, taking the
  `lo` branch whenever it is not zero and `hi` otherwise. That reaches a monomial `m` of `d` that is
  minimal under divisibility: a monomial strictly inside `m` would have to leave the path at a node
  whose `lo` is zero, and it cannot. (iii) Set the inputs in `m` to 1 and the rest to 0. Then `d`
  evaluates to 1. The point is completed through both circuits' rules by `TriangularRules::complete`,
  which evaluates the ANF tails and never touches the manager. The point is returned only if
  `u ≠ v` there. Otherwise the result is `Internal`. The witness is deterministic for a fixed order.
- **Refusals** carry no verdict. "Probably equivalent" is never an output.

## 3. The algorithm: one bottom-up sweep

#1168's `normal_form` is top-down and recursive, so a single target's normalization generates all
the garbage before control returns. That leaves no point at which collection can run. The consumer
restructures it as a sweep, which changes the schedule but not the mathematics:

1. **Cone of influence.** A DFS from the paired outputs over the tails marks the heads that matter.
   Rules outside the cone are never converted or normalized. Cost: O(Σ tail terms).
2. **Fan-out counts** for each cone head: how many cone tails read it, plus one if it is an output.
3. **Sweep** the cone heads from the bottom of the order up. For head `s`:
   convert its tail to a ZDD just in time (sparse `build`), then compute `nf[s]`. This is llnf
   (Dagstuhl 10271 Alg. 1) where every rule lookup reads an already-swept `nf[t]` instead of
   recursing into `t`'s tail, so the recursion never leaves `s`'s own tail. Then decrement the
   fan-out of every head `s`'s tail reads, and release any `nf[t]` that reaches zero.
4. **Compare** as soon as both members of a pair are swept, then release both. The first mismatch
   stops the sweep and goes to the witness (§2.3).
5. **Simulate** (only on `Equivalent`), then drop the manager.

The live set at any moment is the **frontier**: `nf[t]` for swept heads with fan-out remaining,
plus outputs waiting for their partner. This is the classical memory profile of BDD-based
combinational equivalence checking.

In v1, the sweep schedule is fixed by the variable order, so a scrambled order scrambles both the
diagram order and the schedule. Decoupling the two is a non-goal (§9).

## 4. Garbage collection

### 4.1 Design: mark-and-sweep at safe points

- **Safe points** fall between two heads of the sweep (§3 step 3), and nowhere else. Between heads,
  no intermediate result lives on the Rust stack, so the root set is exact:
  `{ZERO, ONE} ∪ {nf[t] : t on the frontier}`. Tails are converted just in time and are not roots.
- **Trigger.** Collect at a safe point when the slots allocated since the last collection reach
  `max(2^16, live after the last collection)`. The threshold doubles with the live set, so the total
  GC work is a constant times the total allocation (§4.2). At a safe point, a collection is also
  forced if the slots in use exceed half the node budget.
- **Mark.** Iterative DFS from the roots into a mark bit vector, 1 bit per slot, reused between
  collections.
- **Sweep.** Unmarked slots join a free list threaded through their `hi` field, so it costs no extra
  bytes. Freed slots are poisoned (`level = POISON`), and in debug builds any read of a poisoned
  slot panics. `mk` pops the free list before it grows the vector.
- **Ids never move.** There is no compaction, so the frontier's ids stay valid across a collection,
  and no handle needs rewriting. Canonicity survives. No live node points at a dead one, because
  marking is a transitive closure, and dead triples leave the unique table. A rebuilt triple gets a
  fresh id, and it is the only live node with that triple.
- **Unique table:** `retain` the entries whose id is marked.
- **Operation caches** (`Xor`, `Mul`, `NormalForm`) are **cleared completely**. A reused slot
  would otherwise alias a stale cache entry to a new node. That is the one hazard of slot reuse, and
  clearing is the simplest rule that rules it out. Caches keyed on dead ids are the usual case
  anyway. The sharing the `NormalForm` cache provided across targets in #1168 is now carried by
  `nf[·]` on the frontier.
- **Budget semantics.** The node budget bounds slots in use (live plus garbage not yet swept), not
  total allocations. Within one head, garbage cannot be collected in v1. A single head whose
  normalization exceeds the budget is a typed `NodeBudgetExceeded`, as in #1168.

### 4.2 Cost

| part | cost per collection | notes |
|---|---|---|
| mark | O(live nodes) | the frontier's shared size |
| sweep of the node vector | O(slots) | linear scan of the mark bits |
| unique-table `retain` | O(unique-table capacity) | the dominant term in practice |
| cache clear | O(cache capacity) | plus the recomputation it causes, which is counted in the sweep's own time |
| memory | slots / 8 bytes for mark bits; free list costs nothing extra | the capacity of the tables does not shrink, so heap-by-capacity remains a peak figure |
| hot path | nothing | no counter updates in `mk`, `xor` or `mul` |

With the doubling trigger, the total collection work is O(total allocations + number of
collections × table capacity), and the second term is bounded by the same doubling. G3 (§7)
measures the cost on families with almost no garbage, where it is pure overhead, and the effect on
chi8, where the garbage is.

### 4.3 Reference counting, costed and rejected for v1

Reference counting (CUDD-style, with deferred deletion) would free garbage *within* a head. It
costs a `u32` count per node (a 12-byte node becomes 16 bytes, +33%), an update on every `mk` and on
every cached result, and ref/deref discipline in every recursive operation. Each `?` early return on
a budget refusal is a leak unless a guard type handles it. It puts cost on the hot path of every
family to save memory on one family. §3's sweep already gives collection a precise root set at
zero hot-path cost. If G3's effect gate fails because the garbage *within a head* dominates, RC is
the recorded next design, and a new proposal is needed.

## 5. Full cost accounting

Every stage below is inside the consumer's complete-task time `T_Z`. Nothing is excluded except as
stated.

| stage | work | bound | in `T_Z`? |
|---|---|---|---|
| read the instance | parse the instance file the harness also feeds to the other routes | O(input size) | yes (whole-process wall) |
| verify | triangularity (§2.2.1), coverage (§2.2.2), pairs (§2.2.3) | O(Σ tail terms × term length) | yes |
| cone and fan-out | §3 steps 1–2 | O(Σ tail terms) | yes |
| conversion in | sparse ANF → ZDD, per tail, just in time | O(tail terms × term length) per head | yes |
| sweep | llnf per head on the frontier | the measured quantity | yes |
| GC | §4.2 | the measured quantity, also reported on its own | yes |
| compare | one id comparison per pair | O(pairs) | yes |
| certification, `Equivalent` | 1,024-vector bitsliced simulation of both circuits | 16 words × Σ tail terms × term length | yes |
| certification, `Differ` | one XOR, a path walk of length ≤ vars, completion, re-evaluation | O(vars + Σ tail terms) plus one XOR | yes |
| conversion out | **none**: no `to_anf` is on any path | 0 | — |
| failed attempts | a budget refusal ends the call. **The consumer never retries** in another order or with a larger budget. A refused attempt's time is recorded and censored, and at a gating size it fails the gate rather than leaving an absent row | — | recorded |
| teardown | drop the manager | O(capacity) | yes |

**The comparand routes face the same contract**, so the ratios compare like with like:

- **A (expanded ANF, the #1168 baseline).** Same read, verify and cone stages. For each pair,
  `anf_normal_form(x_u + x_v)` with the 2^21-term budget, then a zero test. On a nonzero result, a
  minimal monomial gives the witness, which gets the same independent re-check. Simulation runs on
  `Equivalent`. A term-budget refusal is censored.
- **K (kissat 4.0.4, the pinned `tools/external/provision-sat.sh` build).** The miter as CNF: the
  #220 encoding (one Tseitin AND per monomial, XORs cut at 4) of every rule, plus `d_k = u_k + v_k`
  and one clause `d_1 ∨ … ∨ d_m`. `T_K` is the kissat process's wall time. CNF generation is
  reported separately and **not charged to K**, which is generous to K. A SAT model is projected to
  `X` and re-checked like a `Differ` witness. A wrong model is an invalid row, and it is reported.
- **CryptoMiniSat 5.18.0 with Gauss–Jordan** on the same miter, with its XORs native. This is
  reported only.
- **Z0 is Z with GC disabled.** It exists only for G3.

## 6. Fixtures

All fixtures are public and generic, and extend `src/boolean/fixtures.rs`. Private cryptanalysis
models stay in the private repository. Each structured family is a pair of **structurally
different** circuits for the same function.

| id | family | circuit A | circuit B | sizes |
|---|---|---|---|---|
| S1 | adder-n | ripple carry (#1168's) | Kogge–Stone prefix adder. Its operator `(G, P)∘(G', P') = (G + P·G', P·P')` is exact in ANF, because `G·P = 0` | n = 8, 12, 16, … |
| S2 | ladder-n | `t_i = (t_{i-1} + a_i)(b_i + c_i)` | distributed: `u_i = t_{i-1}(b_i + c_i)`, `w_i = a_i(b_i + c_i)`, `t_i = u_i + w_i` | n = 8, 12, 16, … |
| S3 | chi8-r | #1168's chi-SPN | chi through intermediates (`m_j = (x_{j+1} + 1)·x_{j+2}`, `y_j = x_j + m_j`), and the mix re-associated `(y_j + y_{j+1}) + y_{j+3}` | r = 2, 3, 4, … |
| C1 | dense MQ-k (adverse) | #1168's control | each `q_j` split into two fresh signals holding random halves of its terms, and the same for the target | k = 10, 20, 30, …, 3 seeds |

- **Mutants (contract C).** For every S instance, 3 mutants of B, each deleting one uniformly
  random tail term of one uniformly random cone rule (fixed seeds). A mutant is kept only if K
  reports SAT, so ground truth comes from an independent tool. Mutants that K reports UNSAT are
  equivalent by accident. They are discarded and counted.
- **Orders.** The *natural* order is reverse creation order, with A's and B's rules interleaved by
  output bit. There are also **5 scrambled topological orders** per instance: uniformly random
  linear extensions of the miter's dependency DAG, inputs included, exactly as #1168 defines them.
  Scrambled rows are reported separately and never pooled with natural ones.
- **Ladders.** Route A stops at its first refusal. Z, Z0 and K continue past that point, up to the
  first refusal, a 600 s attempt cap, or a 16 GiB `tools/rss-guard.sh` ceiling, with a ceiling of
  n = 4,096 (S1, S2), r = 64 (S3) or k = 64 (C1). The G2 rows need sizes where Z is no longer
  sub-millisecond.

## 7. Predeclared go/no-go (bench-host figures)

This section is fixed when the proposal is accepted and is not edited after any measurement is
read. If a gate proves ill-posed, the verdict note says so and applies it as written.

### 7.1 Measurement

- **Bench host only.** Single-threaded, inside a `tools/bench-reserve.sh` reservation, submitted as a
  `tools/bench-job` manifest. Each attempt is a fresh process. The build is the current release
  profile, and its `build` stamp is recorded. The commit goes beside every figure, and
  `tools/check-measurement-provenance.sh` must pass.
- **n = 9 repetitions** per cell, with the single predeclared extension to 21 when a verdict is
  inconclusive. Contamination follows `benchmarking.md`'s rule, and a session with more than 20%
  contaminated attempts is void.
- **Statistics** come from `tools/bench_stats.py`. Z ÷ A and Z ÷ Z0 are *paired* by repetition
  (same binary, different arms). Z ÷ K is *independent*. The small-row rule applies: a row under
  300 ms never wins.
- **Memory** is the peak RSS per attempt on Linux, plus the manager's heap by capacity as #1168
  reports it.

### 7.2 Gates

Each gate has exactly one comparator (`development.md`, *Gating a performance candidate*). The
other ratios are reported beside each gate and decide nothing.

**G1: representation, against route A.**
In **at least two of S1–S3**, on the equivalent pairs:

1. Natural order: `R = T_A / T_Z` has a **lower 95% bound ≥ 10** at **each of the two largest
   sizes at which A completes**.
2. At the larger of those two sizes, the **median over the 5 scrambled orders** of R is ≥ 10, and Z
   completes in **≥ 4 of the 5** scrambled orders. A scrambled order in which A refuses and Z
   completes counts as R = +∞.
3. At those sizes, Z's peak RSS is ≤ A's peak RSS and ≤ 256 MiB, and Z has no refusal at any size
   up to them.

**G2: user value, against kissat (K).**
In at least one family that passes G1, at **each of the two largest sizes at which Z completes**:
Z wins (`win_verdict` on `T_Z / T_K`, small-row rule applied), **or** K is censored at the 600 s
cap while Z completes. CryptoMiniSat is reported beside this gate.

**G3: garbage collection, against Z0.**

1. *Cost:* on S1 and S2 at G1's sizes, the paired `T_Z / T_Z0` passes `regression_verdict` at a
   bound of **1.10**.
2. *Effect:* on S3 at its two largest A-complete sizes, Z's **peak slots in use are ≤ 0.5 ×** Z0's
   allocated nodes, with the same verdicts.

**G4: correctness. Any failure is NO-GO regardless of speed.**
Every equivalent pair returns `Equivalent`. Every kept mutant returns `Differ` with a witness that
passes the independent re-check. There are zero `Internal` results and zero simulation
disagreements. Z and A agree on every row where both complete, as do Z and K. In the test suite,
the outcomes under GC stress (collect at every safe point) equal those under GC off. Verdicts are
compared, and so is each normal form's ANF at small sizes.

**G5: fail-safe on the adverse control (C1).**
C1 is expected to lose (R ≤ 1, as in #1168, where R fell from 1.0 to 0.6 by k = 40). It never
counts toward GO, and its ratios are reported. What *is* gated is that every C1 attempt, in natural
and scrambled orders, **either completes correctly or returns a typed `Budget` refusal**, and none is
killed by the RSS ceiling. The budget, not the machine, must be what stops it.

### 7.3 Disposition

| G1 | G2 | G3 | G4, G5 | disposition |
|---|---|---|---|---|
| pass | pass | pass | pass | **GO**: authorizes a follow-up proposal for the checker as a documented, opt-in API (still feature-gated, no default, no dispatch) |
| pass | fail | pass | pass | **GO, research only**: the representation gain survives into a consumer, but kissat already serves the user better. The module stays as research evidence, with no public API, and this is recorded |
| pass | any | fail | pass | **NO-GO on this GC design**: record whether the garbage is within a head (which points to RC, §4.3) or the cost is too high (which points to the trigger). A revised GC is a new proposal |
| fail | — | — | pass | **NO-GO**: the representation gain does not survive a consumer, and no further ZDD work happens without new evidence |
| any | any | any | fail | **NO-GO** until fixed, whatever the timings |

The checker is opt-in and called by name. It never sits behind a dispatch rule, so no dispatch gate
applies. C1 measures the harm it can do (G5), not a regime rule.

**Reported qualifiers, never gating:** the spread of R across scrambled orders (max ÷ min), the
share of `T_Z` spent on certification and on GC, how many mutants were discarded, peak frontier
size, and the largest single-head allocation (the case §4.3 is for).

## 8. Scope, budget and stop conditions of the prototype acceptance would authorize

New files under `src/boolean/` and a new example, all behind `research-zdd`:

| part | estimate, non-test lines |
|---|---:|
| sparse rules and the uncapped order for the consumer | 120 |
| route A on sparse terms (substitution with a term budget) | 100 |
| sweep, cone, fan-out, compare | 150 |
| GC (mark, sweep, free list, poison, trigger) inside the manager | 180 |
| witness, completion, bitsliced simulation | 120 |
| fixtures: prefix adder, distributed ladder, re-associated chi, split MQ, mutants | 200 |
| harness and CNF export (reusing `sat_algebra`'s encoding) | 350 |

That totals about **1,200 lines**. Stop conditions, which bind:

- If the work exceeds **1,500 net lines**, stop and record why.
- If GC needs node ids to move (compaction), or needs a change outside `src/boolean`, stop. That
  is a different design.
- Laptop runs are development figures only and decide nothing. The verdict is the bench-host run
  in §7.
- After a NO-GO, stop. No tuning, no ordering heuristics, no retries.

## 9. Non-goals and constraints that do not change

- **No change** to `Monomial`, the `GF(2)` field types (`Zp2`, `BinaryFieldElement`, the packed
  rows), any default, `F4Options`, any planner or dispatch, or `src/grobner`, `src/linalg` and
  `src/fields`. Nothing in the crate calls the checker.
- **Not #1156's work.** There is no Gray-code enumeration, no crossbred split and no Macaulay
  preprocessing. Nothing touches the `GF(2)` packed elimination.
- **No SAT backend.** kissat and CryptoMiniSat are external comparands run as processes, under #220's
  policy. No C dependency is added, and no solver is linked.
- **No ANF output API**: `R_out` is the case this proposal exists to avoid. Contract A is not
  adopted (§2).
- **No dynamic reordering** (sifting) and no ordering heuristic. Orders are given. A schedule
  independent of the order is out of scope too.
- **No sequential circuits**, no latches and no unrolling. Combinational miters only.
- **No multipliers as a target.** Multiplication is the known hard case for decision diagrams.
  Bryant's 1991 lower bound is for BDDs, and the ANF-ZDD here is a different diagram, so nothing
  is claimed either way.
- **No private cryptanalysis models**, and no new Cargo dependency.
