# The multivariate GCD routes, measured: the default is right for the opposite reason

**Measured at:** `261b9540` plus the change that adds `examples/gcd_routes.rs` — both arms are
existing entry points selected by `GcdRoute`, so there is no before-side tree to name and nothing
merged after `261b9540` can have moved one arm relative to the other. `261b9540` is a merge commit
on `main` and so stays resolvable
([#505](https://github.com/mfaulk/zeebra/issues/505)).

Measurement record for #407. #128 landed the primitive PRS and published **no timings at all**;
Collins' subresultant PRS then became the default on correctness evidence plus an asserted
*operation count*, with the wall clock explicitly deferred. So before this there was no duration
figure for either route.

Machine: AMD Ryzen Threadripper PRO 5995WX, 128 hardware threads, 503 GB RAM. One core
(`taskset --cpu-list 12`), release profile with the repository's defaults, `RUSTFLAGS` unset,
`RUSTC_WRAPPER=""`, a per-worktree `CARGO_TARGET_DIR`, under
[`tools/benchlock.sh`](../../tools/benchlock.sh). ISA floor `x86-64-v3 or better (AVX2)`, printed in
the run's own header. Each figure is the fastest of up to 5 interleaved repetitions; the `reps`
column in the raw output says how many a shape actually got, and rows that got one are single-shot.

**Durations here are shared-machine durations.** Other agents build and measure concurrently on this
box; `benchlock` excludes other measurements and does nothing about shared L3 or memory bandwidth.

## 0. The result, which is not the one the operation count predicts

The asserted operation count — 18 recursive content GCDs against 6 on a degree-five-against-two
pair — says the subresultant route does less work. **The wall clock says it is usually slower.**

| field | shapes the subresultant route wins by >10% | shapes the primitive route wins by >10% |
|---|---:|---:|
| KoalaBear | 2 | **15** |
| Goldilocks | 3 | **14** |
| BN254 `Fr` | 2 | **16** |

Twenty shapes per field — seven each at two and three variables, six at four — crossing the shared
factor's term count, each cofactor's term count and the largest per-variable exponent. The
subresultant route's typical loss is **10% to 50%**.

**And the default should stay anyway.** The two routes are not slower-and-faster; they are
different-tailed, and the tail is what decides it.

## 1. The primitive route's tail is unbounded; the subresultant route's is not

| | shape | primitive | subresultant | |
|---|---|---:|---:|---|
| **the primitive route's worst** | KoalaBear, 4 vars, 2-term factor x 6-term cofactor, 10 terms | **1.2561 s** | 0.0020 s | **628x** |
| the subresultant route's worst | KoalaBear, 4 vars, 4 x 4, 16 terms | 0.0011 s | **0.0262 s** | 24x |
| a typical row | Goldilocks, 3 vars, 3 x 3, 9 terms | 0.00015 s | 0.00015 s | ~1.0x |

The 628x row got **one repetition**, so it is a single pass rather than a minimum of five — which is
the honest caveat on the largest number here, and it is an order of magnitude clear of anything the
spread could explain.

Worse, there is a shape where the primitive route appears not to terminate on any useful timescale.
The first attempt at this sweep was killed by its own 2 400 s timeout **mid-table**, having
completed KoalaBear's two- and three-variable shapes and six of the seven four-variable ones. The
rows it did print sum to under two seconds. So the seventh four-variable shape — a 5-term factor
against 5-term cofactors at exponent 4 — consumed essentially the whole remaining **~40 minutes**
without finishing, and two of the three fields were never reached.

That shape is now excluded in advance rather than reactively, and the exclusion is printed, because
the cost cannot be bounded after the fact: a single pass of either route is a synchronous call.
**The attribution to the primitive route is inferred, not measured** — the harness runs the
correctness pass primitive-first, and the neighbouring shape has the primitive route 628x slower, so
it is the overwhelmingly likely culprit, but the run died before it could say which arm it was in.

## 2. Why the tails differ, which the theory already said

- **Primitive PRS** removes the content from every pseudo-remainder. A content is itself a recursive
  GCD in a smaller ring, so the cost is a *recursion over recursions*, and nothing bounds how much
  work a step's content costs in terms of the original inputs. Coefficients cannot grow — that is
  the bound it buys — but the recursion is where the time goes, and it is the recursion that
  explodes.
- **Subresultant PRS** replaces that with one exact division by `g * h^delta`. The sequence's
  entries *are* subresultants, determinants of submatrices of the inputs' Sylvester matrix, so
  Hadamard's inequality bounds them in terms of the inputs alone. There is no recursion to explode;
  the cost is the growth, and the growth is bounded in advance.

So the measured picture is the theoretical one with the emphasis moved: the subresultant route pays
a steady 10–50% to buy a bounded worst case, and the primitive route takes a better median in
exchange for a tail that reaches 628x and, on at least one shape, does not land.

## 3. What this changes

**The default does not move.** `GcdRoute::SubresultantPrs` stays, and the justification in the
source changes from "correctness evidence, not a measurement" to a measurement — of the tail rather
than the median. A library default should be the route that cannot fall off a cliff on an input the
caller did not know was special, which is the usual argument for a bounded worst case over a better
average, and it is now supported by numbers rather than by the operation count.

**`PrimitivePrs` stops being only a reference implementation.** It is 10–50% faster on most shapes,
which makes it a legitimate choice for a caller who knows its inputs, and `gcd_by` already exposes
it. That is worth stating in the README, where it was previously described only as the route the
other is tested against.

## 4. What this does not establish

* **Brown's modular algorithm.** #407 names it as the second route and it is not implemented, so
  the comparison here is between the two that exist. It is the route that changes the asymptotics,
  and it is #434.
* **A shape-aware default.** The two routes' costs differ by up to 628x in one direction and 24x in
  the other on *neighbouring* shapes, which is the signature of a choice that wants to be made per
  input rather than once. Nothing here measures a predictor — term count, arity and exponent are
  the three axes swept and none of them separates the 628x row from its neighbours on its own.
* **Where the primitive route's blow-up comes from.** Attributed to the content recursion by the
  theory and by the shape of the measurement, not by a profile.
* **Any instance from the solver.** These are planted-factor random inputs. What F4 and FGLM
  actually hand `gcd` is unmeasured, and that is the input distribution a default should really be
  chosen against.

## 5. Reproducing

```sh
export CARGO_TARGET_DIR=/path/outside/the/worktree RUSTC_WRAPPER=""
unset RUSTFLAGS
cargo build --release --example gcd_routes
tools/vec_census.sh "$CARGO_TARGET_DIR/release/examples/gcd_routes"

tools/benchlock.sh <tag> taskset --cpu-list 12 \
  cargo run --release --example gcd_routes
cargo run --release --example gcd_routes -- bn254   # one field
```

The binary asserts the two routes equal at every shape before timing it, prints the ISA floor and
the repetition count per row, and reports which shapes it omitted and why.
