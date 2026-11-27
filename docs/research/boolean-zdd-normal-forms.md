# Bounded ZDD normal forms for structured Boolean systems (#1168)

**Status:** prototype complete, 2026-11-27. **Disposition: GO, qualified, under the predeclared
criterion (§6).** On two of three structured families (adder and AND/XOR ladder), the ZDD normal form
beats the expanded-ANF route by 10^3–10^4× at the largest sizes the ANF route completes. Its state
is kilobytes against megabytes. The third family (toy chi-SPN) fails the criterion, and the dense
MQ control is at or below parity, as expected. The win is in the **representation of the result**,
not in avoided intermediate swell. Converting the results back to ANF leaves a 2–4× gain (§7). A GO
here authorizes a separate proposal and nothing else: no solver integration and no default change.

**Measured at:** `2eb16995` (branch `research/1168-zdd-normal-forms`), `examples/zdd_normal_forms.rs
--mq-max 40` in release, thin LTO, codegen-units 16, one process, 570 s. macOS arm64 laptop (M4 Pro,
14 cores, 48 GiB), unpinned, shared with four concurrently building agents (load average 8–23 during
the session). **Development figures only.** They satisfy no deciding-measurement protocol. Per-row
memory is a structural estimate (§5); the only process RSS figure is a whole-run maximum.

Predeclared criterion: [#1168 comment](https://github.com/mfaulk/zeebra/issues/1168#issuecomment-7223890094),
posted before any implementation or measurement. Parent: #196. Tracker: #1169. Evidence:
[`research/1168-zdd/`](../../research/1168-zdd/) (`results.csv`, `tables.md`, `verdict.txt`,
`summarize.py`).

## 1. Contract

- **Ring.** The Boolean quotient `GF(2)[x_0, …, x_{n-1}] / <x_i^2 + x_i>`, not the polynomial ring the
  rest of the crate works in. `x^2 + x + 1` is `1` here, so it generates the unit ideal. In `GF(2)[x]`
  the same polynomial is irreducible and generates a proper ideal. A test asserts both, using the
  crate's own univariate irreducibility test and multivariate remainder.
- **Result.** The exact Boolean normal form of a polynomial `f` with respect to **verified
  triangular rules** `x_i + h_i`, where `h_i` mentions only variables after `x_i` in a chosen order.
  Together with the field equations, these rules form a lexicographic Boolean Gröbner basis (Dagstuhl
  10271, Thm. 3.1), so the normal form is unique. Both routes must return it exactly.
- **Not** a Gröbner basis computation, a solver, a point or a backend. The rules are checked before
  use. A non-permutation order, a duplicate head, an out-of-range variable, or a tail variable at or
  before its head is refused as a typed `RuleError`.

## 2. What was built

All of it is behind the `research-zdd` feature, in new files only. Nothing in `src/grobner`,
`src/linalg`, `src/fields`, `Monomial` or the GF(2) types changed. The CI research set is
`research-zdd` in `tools/ci-research.sh`.

| file | role | non-test lines |
|---|---|---:|
| `src/boolean/mod.rs` | `VariableOrder`, `ZddError`, `RuleError` | 156 |
| `src/boolean/anf.rs` | square-free ANF oracle (monomial bitmasks, ≤ 256 variables), and the expanded-ANF substitution with a term budget | 226 |
| `src/boolean/zdd.rs` | bounded manager: canonical unique table, one operation cache, node and cache budgets, XOR, Boolean product, substitution `x_i ← h`, ANF↔ZDD, term and node counts | 398 |
| `src/boolean/normal_form.rs` | rule verification, the ZDD normal form, the ANF route | 138 |
| `src/boolean/fixtures.rs` | the families and scrambled orders (§4) | 179 |
| `examples/zdd_normal_forms.rs` | the measurement and the mechanical verdict | 412 (whole file) |

Items 1–4 of the issue total **918 lines** including doc comments. That is under the ~1,000-line
budget. No garbage collection or dynamic reordering was needed to reach the go/no-go, so the stop
condition did not fire. §7 explains why a backend would need GC.

**Representation.** A node `(level, hi, lo)` is `x·hi + lo`. The *then* arc means "the variable
is present in the monomial", and a node whose `hi` is zero is never built (Minato's zero
suppression). Level 0 is the top of the diagram and the largest variable in lex. That matches
Dagstuhl 10271 §2.2, Defs. 2.2–2.3.

**Product.** With `x` the top variable, `f·g = x·(f1·g1 + f1·g0 + f0·g1) + f0·g0`. The square
`x^2` folds into `x` here, and `f·f = f` is a constant-time early exit.

**Normal form.** This is Dagstuhl 10271 Alg. 1 (`llnf`), with the rules indexed by level instead of
encoded as one diagram. With `x` at `f`'s top, `f = x·f1 + f0`, and the result is either
`mk(x, nf(f1), nf(f0))` when `x` is free, or `nf(h)·nf(f1) + nf(f0)` when a rule defines `x ← h`.
Results are cached per node.

**Refusals.** `NodeBudgetExceeded`, `CacheBudgetExceeded`, and `TermBudgetExceeded` (for ANF output)
are values, never truncations. Measured budgets: 2^23 nodes, 2^25 cache entries, 2^21 terms per
ANF polynomial.

**References.** *Network-driven Boolean Normal Forms* (Brickenstein and Dreyer, Dagstuhl 10271,
CC-BY) was read in full: Algs. 1–3, §4's topological and rank orderings, and Tables 1–2. The JSC 2009
PolyBoRi paper could not be retrieved from this environment: the DOI resolves to Elsevier, which
returned 403, and no repository copy was listed. Its representation is restated in Dagstuhl §2.2,
which is what this prototype follows. PolyBoRi/BRiAl is GPL. No code was read or reused; the code
here is written from the published algorithms.

## 3. Correctness

Run with `cargo test --features research-zdd --lib boolean` (19 tests) and `--example zdd_normal_forms`:

- **Conversion round trips.** ANF→ZDD→ANF is the identity on random polynomials in scrambled
  orders, and `term_count` equals the ANF length.
- **Canonicity.** `f + g` built by `xor` and `g + f` built from ANF have the same root id.
- **Boolean identities.** `f·f = f`, `f + f = 0`, and `f·(g + h) = f·g + f·h` hold on random
  diagrams.
- **Operations against the oracle.** ZDD product and substitution equal the ANF product and
  substitution.
- **Normal form.** The ZDD normal form equals the ANF route on random triangular systems in random
  orders. `NF(NF(f)) = NF(f)` by root id, and no rule head survives.
- **Exhaustive truth tables** (n = 9, all 512 free assignments, completed through the rules): `f`
  and `NF(f)` agree on every point the rules cut out.
- **Zeebra's multivariate arithmetic.** The normal form equals `normal_form` from
  `MultivariatePolynomial<10, Zp2>`, run modulo the rules **plus explicit `x^2 + x`** in lex with
  the diagram's order. The same holds for all 25 random systems.
- **Refusals.** Non-triangular, duplicate-head and out-of-range rules are refused, and the same
  rule is accepted in an order that puts its head first. Node, cache and term budgets each refuse.
- **Fixtures.** The adder adds: on every 3-bit input pair, its normal forms evaluate to `a + b`.
  Every family, under natural and scrambled orders, agrees with the ANF route.
- **Every measured row** asserts that the two routes return identical results whenever both
  complete.

Mutation check: dropping the `f0·g1` term from the product fails 6 tests, and using an unreduced
rule tail in the normal form fails 4.

## 4. Fixtures and orders

These are public and generic. Private cryptanalysis models stay in the private repository.

- **adder-n:** an n-bit ripple-carry adder. The targets are the sum bits and the carry out.
- **ladder-n:** `t_i = (t_{i-1} + a_i)·(b_i + c_i)`. The target is `t_n`.
- **chi8-r:** width 8 and r rounds. Each round is a chi layer `y_j = x_j + (x_{j+1}+1)·x_{j+2}`
  followed by the mix `z_j = y_j + y_{j+1} + y_{j+3}`. The targets are the final state.
- **mq-k (control):** k inputs, k rules `y_j = q_j(x)`, and a target `q(y)`. Every `q` is uniformly
  random dense quadratic. There are 3 seeds per size.

The **natural order** is reverse creation order. A **scrambled order** is a uniformly random
topological order: a random linear extension of the dependency DAG, inputs included. Every scrambled
order therefore keeps the rules triangular, which is the only kind of scramble the contract admits.
There are 5 scrambled orders per instance, reported separately.

The **ANF route** substitutes heads into each target from the top of the order down. That takes one
pass, since a tail never reintroduces an earlier head. Each ladder stops at the first size where
either route refuses, or where a run exceeds 30 s.

## 5. Results

R is the ratio T_anf / T_zdd for the complete routes. The ZDD route includes rule verification and
the ANF→ZDD conversion of the rules and targets; the ANF route includes rule verification. Times are
the median of 5 runs. R_out adds the ZDD→ANF conversion of every result, timed once.

"ZDD heap" is the manager's tables by capacity: the node vector, the unique table and the cache. The
manager frees nothing, so this is also its peak. "ANF KiB (lb)" is a lower bound: one hash table of
the peak intermediate size, at 33 bytes per term. The whole run's maximum process RSS is in
`verdict.txt`.

Natural-order figures, structured families (`research/1168-zdd/tables.md` has every row):

| family | size | vars | ZDD ms | ZDD out ms | ANF ms | R | R_out | scrambled R (median) | alloc nodes | result nodes | result terms | ZDD heap KiB | ANF peak terms | ANF KiB (lb) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| adder | 16 | 64 | 0.052 | 10.1 | 63.4 | 1229 | 6.27 | 933 | 155 | 63 | 131,086 | 8.6 | 65,535 | 2,112 |
| adder | 18 | 72 | 0.062 | 68.8 | 248.8 | 4041 | 3.62 | 2656 | 175 | 71 | 524,304 | 8.6 | 262,143 | 8,448 |
| adder | 20 | 80 | 0.067 | 283.6 | 1048.2 | 15664 | 3.69 | 11363 | 195 | 79 | 2,097,170 | 10.4 | 1,048,575 | 33,792 |
| adder | 22 | 88 | 0.073 | refused | refused | — | — | — | 215 | 87 | 8,388,628 | 10.4 | — | — |
| ladder | 14 | 57 | 0.029 | 3.3 | 7.9 | 274 | 2.34 | 145 | 96 | 43 | 49,150 | 5.2 | 49,150 | 1,584 |
| ladder | 16 | 65 | 0.036 | 14.2 | 41.1 | 1130 | 2.89 | 808 | 110 | 49 | 196,606 | 5.2 | 196,606 | 6,336 |
| ladder | 18 | 73 | 0.041 | 92.5 | 210.7 | 5171 | 2.28 | 3075 | 124 | 55 | 786,430 | 7.1 | 786,430 | 25,344 |
| ladder | 20 | 81 | 0.043 | refused | refused | — | — | — | 138 | 61 | 3,145,726 | 8.6 | — | — |
| chi8 | 6 | 104 | 6.7 | 0.08 | 33.5 | 5.0 | 4.95 | 7.2 | 16,736 | 414 | 1,064 | 1,812 | 925 | 29.8 |
| chi8 | 7 | 120 | 9.5 | 0.09 | 45.1 | 4.7 | 4.70 | 11.1 | 20,388 | 419 | 1,080 | 2,764 | 925 | 29.8 |
| chi8 | 8 | 136 | 18.2 | 0.19 | 56.4 | 3.1 | 3.08 | 10.4 | 23,838 | 420 | 984 | 2,764 | 925 | 29.8 |

At adder-22 and ladder-20, the ZDD route still finishes in 0.07 ms and 0.04 ms. Only the ANF route
and the conversion out refuse, because the results have 8.4 M and 3.1 M terms. Expanded-ANF terms
avoided (result terms minus result nodes) are 2,097,091 at adder-20 and 786,375 at ladder-18.
Unique-table and cache hit counts are per row in `results.csv`. At chi8-8, for example, there are
222,395 cache lookups with 151,195 hits (71,200 entries held), and 67,218 unique-table lookups with
43,380 hits.

**MQ control** (natural order, median over 3 seeds). This ladder was capped at k = 40 with
`--mq-max 40`, because the control grows about k^6 and neither route refuses before the example's
k = 64 limit. A full ladder would have taken hours on a shared laptop. The cap is not part of the
predeclared criterion, and MQ does not gate.

| k | vars | ZDD ms | ANF ms | R | R_out | scrambled R | alloc nodes | result nodes | result terms | ZDD heap KiB | ANF KiB (lb) |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 10 | 20 | 0.56 | 0.56 | 1.0 | 0.98 | 0.9 | 2,795 | 124 | 193 | 227 | 13.6 |
| 20 | 40 | 19.2 | 15.7 | 0.8 | 0.80 | 0.8 | 77,518 | 1,446 | 3,077 | 7,248 | 153 |
| 30 | 60 | 170.4 | 117.5 | 0.7 | 0.71 | 0.7 | 512,862 | 6,967 | 16,065 | 51,840 | 699 |
| 40 | 80 | 867.4 | 521.4 | 0.6 | 0.62 | 0.6 | 2,123,955 | 22,792 | 50,894 | 231,936 | 2,116 |

R falls from parity to 0.6, and the manager's state is 74–110× the ANF bound at k = 30–40, mostly
unreclaimed intermediates. That is the expected adverse behaviour.

## 6. The predeclared verdict, applied as written

The evaluation is mechanical (`verdict()` in the example). Its output is in `verdict.txt`.

| criterion | adder (18, 20) | ladder (16, 18) | chi8 (7, 8) |
|---|---|---|---|
| (1) R ≥ 10 at both of the two largest ANF-complete sizes | 4041, 15664 ✓ | 1130, 5171 ✓ | 4.7, 3.1 ✗ |
| (2) ZDD peak ≤ ANF peak, ≤ 256 MiB, no ZDD node/cache refusal | 8.6 vs 8,448 KiB; 10.4 vs 33,792 KiB ✓ | 5.2 vs 6,336; 7.1 vs 25,344 KiB ✓ | 2,764 vs 29.8 KiB ✗ |
| (3) correctness | ✓ (§3, and every row's agreement assertion) | ✓ | ✓ |

Two of three families meet the criterion, so the result is **GO**.

- **Order-dependent?** No. Median scrambled R at the largest size is 11,363 for adder and 3,075
  for ladder, well above 1.
- **Output-bound?** Not by the letter. R_out at the two largest sizes is 3.62 and 3.69 for adder,
  and 2.89 and 2.28 for ladder, all ≥ 2. But ladder is within noise of the bound: the first
  discarded run (§8) read 1.98 at ladder-18. Read ladder as **output-bound in practice**.
- **MQ** is the adverse control and does not count toward GO (§5).

## 7. What the GO means, and what it does not

- **The gain is the result's representation, not avoided intermediate swell.** On adder and ladder,
  the ANF route's peak intermediate is the size of its output: ladder's peak terms equal its result
  terms exactly. The expanded route does no wasted work here; its output is simply exponentially
  large, while the canonical ZDD of that output has 55–79 nodes. A consumer that accepts the result
  **as a ZDD** sees 10^3–10^4×. A consumer that needs ANF out pays the enumeration and sees only
  2–4× (R_out), a constant factor. Any proposal therefore has to name a consumer that takes the
  diagram itself. Equivalence checking, whose normal form is `0` (the Dagstuhl §4.3 use case), is
  the natural one.
- **chi8 shows the limits.** Width 8 bounds every output to 2^8 monomials, so ANF never swells (925
  peak terms at every r ≥ 4). The ZDD route is still 3–5× faster in natural order and 7–11× in
  scrambled orders, where the ANF substitution order swells more. But the manager's state is 2.7 MiB
  against 30 KiB. Allocated nodes grow linearly with rounds (23,838 at r = 8) while the results
  hold about 420. That is garbage the prototype never frees. **Any backend needs garbage
  collection**, which the issue's stop condition puts out of scope here.
- **The dense MQ control** behaves as expected (§5): random quadratics share almost nothing, so
  the diagram is the ANF with pointer overhead and unreclaimed intermediates. R is 0.6 at k = 40.
- **The baseline is naive by design.** The ANF route uses hash-set terms and pairwise products. A
  tighter ANF implementation, such as sorted bitmask vectors, would change its constants but not the
  asymptotic gap on adder and ladder. That gap is the output size itself.
- **Not evidence:** any single expression. The criterion required two families at two sizes each.

## 8. Limits of these figures

- Laptop, unpinned, under heavy concurrent load. Times varied by up to 2× between runs: the first
  discarded run measured adder-16's ANF route at 36.7 ms, against 63.4 ms here. All three runs
  reach the same verdict on the structured families. Every gating ratio is ≥ 1,000× or ≤ 6×, far
  from the threshold of 10, except ladder's R_out discussed above.
- **Two runs were discarded.** The first, at `209163e2`, had a harness that counted a term-budget
  refusal of the *conversion out* as a refusal of the whole ZDD route. That hid the ZDD figures at
  the refusal sizes, contrary to the predeclared "conversion out is secondary", and `6832a175` fixed
  it. The second, at `6832a175`, completed the structured families and was stopped at MQ k = 40 for
  time. `2eb16995` added `--mq-max`, and every figure here comes from one complete run at that
  commit. Neither the criterion nor the fixtures changed.
- Memory is structural: table capacities, and a lower bound for ANF. `peak_resident_bytes` reports
  nothing on macOS, so no per-row RSS exists. The whole run's maximum RSS was 4.6 GiB, against a
  peak memory footprint of 1.2 GiB (`verdict.txt`). It is not attributed per row. The likely source
  is the ANF route at its refusal sizes: it checks the term budget once per row of a product, so it
  can overshoot the budget several-fold before refusing.
- Deciding figures, if a proposal ever needs them, belong on the bench host under the measurement
  protocol.

## 9. Reproduce

```bash
cargo test --features research-zdd --lib boolean
cargo test --features research-zdd --example zdd_normal_forms
CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
  cargo run --release --features research-zdd --example zdd_normal_forms -- \
  --mq-max 40 --out research/1168-zdd/results.csv 2> research/1168-zdd/verdict.txt
python3 research/1168-zdd/summarize.py > research/1168-zdd/tables.md
```
