# Polynomials

Multivariate arithmetic and its dense layouts, GCD and squarefree decomposition, composition,
univariate factorization, and permutation polynomials.

`MultivariatePolynomial<N, F>` is sparse: a monomial-to-coefficient map over `N` variables, held
canonically. No coefficient is ever zero, so the zero polynomial is the empty set of terms and a
monomial whose coefficients cancel is dropped rather than kept at zero. Equality and `Hash` are
over that set, which is why the invariant is not cosmetic — a surviving zero term would make a
polynomial unequal to its own canonical form.

The map is keyed by `MonomialHasher`, not by the standard library's `SipHash-1-3`. A monomial is
`[u32; N]` of small exponents produced by the computation itself, so resistance to adversarially
chosen keys buys nothing and costs more per key than the arithmetic it guards; the replacement is a
multiplicative word hash with a `splitmix64` finalizer, and `MonomialMap<N, V>` / `MonomialSet<N>`
are the aliases that carry it. Two consequences worth stating. The finalizer is not optional —
without it the low bits of a multiplicative accumulator depend only on the low bits of the key,
which is exactly what `hashbrown` buckets on, and small exponent vectors collide in droves; the
tests in `src/poly/multivariate/monomial_hash.rs` compare bucket spread and worst-case bucket load
against the standard hasher on real Gröbner-basis supports so that cannot regress silently. And the
hash carries no per-process seed, so iteration order of these maps is now a function of their keys
alone. Nothing is supposed to depend on that order — the sites that must not sort instead — but a
latent order-dependence that `RandomState` would have surfaced intermittently will now be
reproducible rather than absent.

## Multiplication dispatches over four dense layouts and one hash route

Multiplication collects as the products are formed, so the live set is bounded by the output rather
than by the term-product count. *How* it collects is chosen per operand pair, because the choice is
worth 3x–5x and no single answer covers every arity:

| route | index | cells | selected when |
|---|---|---|---|
| `Accumulate` | one hash lookup per product | — | the general case |
| `DenseTriangle` | three integer operations | `(d+1)(d+2)/2` | `N == 2`, dense output |
| `DenseBox` | one add — the index is separable | `∏(d_i + 1)` | dense output, box within 24x the simplex |
| `DenseSimplex` | `2(N-1)` table lookups | `C(d + N, N)` | dense output, otherwise |

The dense routes do no hashing at all: `slots[index(a) + index(b)] += ca * cb` needs no monomial
key. What distinguishes them is that `DenseBox`'s mixed-radix index is **separable** —
`index(a·b) = index(a) + index(b)`, so the left operand's index hoists out of the inner loop and the
per-product cost is one add at any arity — while `DenseSimplex` ranks the monomials of total degree
at most `d` and so allocates the tightest dense array there is, at a non-separable index. The box
pays up to about `N!` in cells for that separability, which is why the crossover between them sits
near five variables rather than being an asymptotic argument.

Measured on one pinned core under `tools/benchlock.sh`, dense `p * p` against the hashing route:

| arity | terms | products | `Accumulate` | `DenseSimplex` | `DenseBox` |
|---:|---:|---:|---:|---:|---:|
| 3 | 2 925 | 8.56e6 | 127.23 ms | 40.95 ms | **23.58 ms** |
| 4 | 715 | 5.11e5 | 7.37 ms | 3.56 ms | **2.35 ms** |
| 5 | 462 | 2.13e5 | 5.66 ms | **1.55 ms** | 1.76 ms |
| 3, degrees (40, 40, 1) | 3 362 | 1.13e7 | 278.83 ms / 17.0 MiB | 61.48 ms / 3.3 MiB | **33.28 ms / 620.9 KiB** |

So there is no arity in this range where the dense accumulator stops being worth it, and the lopsided
trivariate row is where it is worth most: its bounding box is 5 043 cells where its total-degree
simplex is 317 750, so the box is both 8.4x faster and 28x smaller than hashing.

The one shape where generalizing the layout **loses** is one term against many — the Gröbner
reduction inner step. There the products do not collide at all, so there is nothing for a dense
accumulator to merge, and at `N = 3` it costs 55.4 µs against the hash route's 48.6 µs. At `N = 2`
the same shape *wins* (29.1 µs against 44.1 µs) because the triangle's index is three operations, so
this is not a conclusion that transfers between arities. The predicate therefore requires the
product count to be at least twice an upper bound on the output's monomial count before taking a
dense route above `N = 2`, and that threshold is not applied at `N = 2`.

Three more routes are reachable by name and never selected, each a measured negative result:
`Materialize` (the pre-#243 reference), `Chunked` and `Heap`. `Heap` is Monagan and Pearce's
heap merge, and its `multiply_sorted` form returns the product in monomial order. It is 2.2x–10x
slower than `Accumulate` as a multiply. As a multiply-then-sort it is faster by up to 1.9x, but
only on collision-poor sparse pairs, and no caller in the crate sorts a product. See
[`heap-multiply.md`](../research/heap-multiply.md).

Re-measure any of this with

```sh
cargo run --release --example multivariate_mul                  # every route, per arity and size
cargo run --release --example multivariate_mul -- max_degree=90  # stop short of the six-round size
cargo run --release --example multivariate_mul -- heap           # heap vs accumulate, with the sort
```

## Add, Sub and scale collect into an operand's own map

`Add`, `Sub`, `Neg` and `scale` **collect into one of their operands' maps** rather than building a
`Vec` of `|a| + |b|` terms and rehashing it into a third map. Which operand is mutated follows the
ownership of the spelling you write, and that is the whole of the optimization:

| spelling | what it allocates |
|---|---|
| `&a + &b`, `&a - &b` | clones one side; for `+` the *larger*, since addition commutes |
| `a + &b`, `a - &b`, `a + b`, `a - b` | nothing — the owned operand's map is merged into |
| `a += &b`, `a -= &b`, `a += b`, `a -= b` | nothing |
| `a.scale(&c)`, `&a * &c`, `&a * c` | clones `a` |
| `a.scale_assign(&c)`, `a * &c`, `a * c` | nothing — the owned polynomial's map is scaled in place |

**`c * a` works too, and allocates what `a * c` does.** The mathematics writes `c·a`, and the
orphan rule is why it took a macro: `impl<F: FiniteField> Mul<MultivariatePolynomial<N, F>> for F`
is rejected, since `F` is a type parameter and so the impl's `Self` type is not local. The impls
are therefore generated per field **struct** — `PrimeFieldElement64<P>` is local for every `P`, so
six invocations in `src/left_scalar_mul.rs` cover every prime, binary modulus and extension the
crate names. Each left-hand spelling delegates to the right-hand one with the *same* ownership, so
`c * a` on an owned `a` reaches `scale_assign` rather than cloning. `scale` stays the route for
code that is generic over `F`, which none of this is reachable from.

It covers `UnivariatePolynomial`, `MultivariatePolynomial`, `Matrix` and `Vector`.

`Matrix` and `Vector` scale the same way: `Matrix::scale_assign` and `Vector::scale_assign` scale
the dense element buffer in place, and `m * &c`, `m * c`, `c * &m` and `c * m` on an owned `m` route
through them rather than collecting a second buffer. `&m * &c` and `&m * c` still allocate, which is
the borrowed contract. Unlike the polynomial's, these forms maintain no sparsity — a dense buffer
keeps its zeroed entries — and the saved allocation has not been benchmarked, since `Matrix`/`Vector`
scaling is on no recorded hot path (the dense F4 kernels work on `DenseRows`).

So an accumulator you own grows in place:

```rust
use zeebra::{fields::Zp13, FiniteField, MultivariatePolynomial, Zero};

let vars = ["x", "y"];
let words: Vec<MultivariatePolynomial<2, Zp13>> = ["x^2 + y", "x*y - 1", "y^2 + x"]
    .iter()
    .map(|s| MultivariatePolynomial::parse(s, vars).unwrap())
    .collect();
let row = [Zp13::new(3), Zp13::new(5), Zp13::new(7)];

// The linear layer of a symbolic permutation: no sum is ever built twice.
let folded = row
    .iter()
    .zip(&words)
    .fold(MultivariatePolynomial::zero(), |acc, (m, word)| acc + word.scale(m));

assert_eq!(
    folded,
    MultivariatePolynomial::parse("3*x^2 + 5*x*y + 7*y^2 + 7*x + 3*y + 8", vars).unwrap()
);

// Scaling by zero is the zero polynomial held as no terms, not as zero coefficients.
let mut vanishing = words[0].clone();
vanishing.scale_assign(&Zp13::zero());
assert!(vanishing.is_zero());
assert!(vanishing.terms().is_empty());
```

## Aliasing

The in-place forms mutate the left operand and never the right, and the borrow checker rules out
the one case that would be ambiguous: `a += &a` does not compile, because `&mut a` and `&a` cannot
coexist. Self-assignment is therefore spelled through a clone — `a += a.clone()` doubles, and
`a -= a.clone()` is the empty polynomial, not a map full of zeros.

What this buys is measured in `tests/multivariate_add_memory.rs` and
`tests/multivariate_mds_fold_memory.rs`, which assert it rather than quoting it. Summing two
11 476-term triangles that cancel to a single term allocates **0 bytes** against **594 944** for
the form that materialized every term, because every merge lands on a monomial already present and
the table never grows — the live set is the output. Folding eight scaled words into one accumulator
peaks at **43 312 bytes** against **84 448**; there the output has to be allocated, so the 2x is
all there is to win.

They are two binaries rather than two tests because the peak is read off a process-wide tracking
`#[global_allocator]`: any allocation anywhere in the process raises it, so a second test's operand
construction lands in the first test's measurement whatever lock guards the measured region. One
test per binary is the only arrangement that makes the counters mean what they say.

## GCD, content, and squarefree decomposition

`F[x_0, ..., x_{N-1}]` is not Euclidean, so `gcd` is recursive: read both polynomials as univariate
in their highest occurring variable, over the polynomial ring in the remaining ones. That
coefficient ring is a UFD and not a field, so the Euclidean step is *pseudo*-division — scale the
dividend by a power of the divisor's leading coefficient instead of dividing by it — and the
content comes out of every remainder, which is what keeps those powers from accumulating. The
classical primitive PRS. The recursion terminates because the coefficients of a polynomial read in
`x_v` do not involve `x_v`, so each content is a GCD in a strictly smaller ring.

| method | what it gives |
|---|---|
| `gcd(&other)` | the GCD, normalized so the lexicographic leading coefficient is one |
| `gcd_by(&other, route)` | the same, by a named `GcdRoute`; panics for `Brown` |
| `try_gcd_by(&other, route)` | the same, returning `GcdError` where a route refuses (`KnownOrder`) |
| `content(i)` / `primitive_part(i)` | the GCD of the coefficients in `x_i`, and the quotient by it |
| `degree_in(i)` / `coefficients_in(i)` | the univariate-in-`x_i` view the recursion is built on |
| `exact_div(&divisor)` | the quotient, or `None` when the division leaves a remainder |
| `derivative(i)` | the formal partial derivative |
| `squarefree_part()` / `squarefree_decomposition()` | the radical, and the factors with multiplicities |
| `squarefree_decomposition_by_radicals()` | the reference route the above is tested against |
| `pth_root()` | the `p`-th root of a `p`-th power, or `None` |

```rust
use zeebra::{fields::Zp13, MultivariatePolynomial};

let vars = ["x", "y"];
let parse = |s| MultivariatePolynomial::<2, Zp13>::parse(s, vars).unwrap();

// Two products sharing one factor.
let shared = parse("x + y");
let f = &parse("x - y") * &shared;
let g = &parse("x*y + 1") * &shared;
assert_eq!(f.gcd(&g), shared);

// Coprime inputs have GCD one, and a nonzero constant is a unit.
assert!(parse("x + 1").gcd(&parse("y + 1")).is_one());

// Read in y, x*y^2 + x is x*(y^2 + 1): the content is x and the primitive part y^2 + 1.
let h = parse("x*y^2 + x");
assert_eq!(h.content(1), parse("x"));
assert_eq!(h.primitive_part(1), parse("y^2 + 1"));

// (x + 1) * (y + 1)^2, decomposed by multiplicity.
let repeated = &parse("x + 1") * &(&parse("y + 1") * &parse("y + 1"));
let mut decomposition = repeated.squarefree_decomposition().unwrap();
decomposition.sort_by_key(|(_, multiplicity)| *multiplicity);
assert_eq!(decomposition, vec![(parse("x + 1"), 1), (parse("y + 1"), 2)]);
```

### Characteristic `p`, where the derivative is blind

Differentiation multiplies a factor of multiplicity `e` by `e`, and in characteristic `p` that is
zero whenever `p` divides `e`. So `f / gcd(f, ∂f/∂x_0, ..., ∂f/∂x_{N-1})` is **not** the radical
in general: for `f = ∏ g_i^(e_i)` that GCD is
`∏_{p | e_i} g_i^(e_i) * ∏_{p ∤ e_i} g_i^(e_i - 1)`, so the quotient is the product of only the
factors whose multiplicity `p` does not divide. Over GF(2) every *even* multiplicity is invisible,
and over GF(2) and GF(2^8) is where this crate runs the whole solving pipeline.

Both are nonetheless computed, because the decomposition exists in characteristic `p` and only the
*method* was restricted. What the GCD leaves is `∏_{p | e_i} g_i^(e_i)`, in which every
multiplicity is a multiple of `p` — so it is a `p`-th power, `pth_root` takes the root exactly, and
recursing on the root finds those factors with their multiplicities divided by `p`. The only
refusal left is the zero polynomial, which is divisible by every square.

```rust
use zeebra::{fields::Zp2, MultivariatePolynomial, SquarefreeError};

let vars = ["x", "y"];
let parse = |s| MultivariatePolynomial::<2, Zp2>::parse(s, vars).unwrap();

// Over GF(2) the whole gradient of x^2 vanishes, and the factor is recovered anyway.
let x = parse("x");
let square = &x * &x;
assert!(square.derivative(0).is_zero() && square.derivative(1).is_zero());
assert_eq!(square.squarefree_decomposition().unwrap(), vec![(x.clone(), 2)]);

// A visible multiplicity and an invisible one in the same polynomial.
let shifted = parse("x + 1");
let f = &square * &(&shifted * &(&shifted * &shifted));
let mut decomposition = f.squarefree_decomposition().unwrap();
decomposition.sort_by_key(|(_, multiplicity)| *multiplicity);
assert_eq!(decomposition, vec![(x, 2), (shifted, 3)]);

// The zero polynomial is the only refusal.
assert_eq!(
    MultivariatePolynomial::<2, Zp2>::zero().squarefree_part(),
    Err(SquarefreeError::Zero)
);
```

The visible half costs **one GCD per multiplicity**: with `P_1` the visible part and
`Q_1 = f / P_1`, the ladder `P_{j+1} = gcd(P_j, Q_j)`, `Q_{j+1} = Q_j / P_{j+1}` has `P_j` the
product of the visible factors of multiplicity at least `j`, so `P_j / P_{j+1}` is the one of
multiplicity exactly `j`. `squarefree_decomposition_by_radicals` is #128's repeated-radical form,
kept as the reference the two are differentially tested against: it pays a whole radical — `N + 1`
GCDs over operands that do not shrink — for each multiplicity, and it still refuses in small
characteristic, which is a true statement about *that* method.

**Not Yun's algorithm, deliberately.** Yun's recurrence is univariate; generalized to `N` variables
honestly it carries a `d_i` per variable and needs `gcd(b_i, d_i^(0), ..., d_i^(N-1))` — `N` GCDs
per multiplicity, worse than the ladder and no better than the radicals it was meant to replace.
The ladder reaches the cost Yun's is wanted for with the gradient taken once rather than once per
level.

The GCD's correctness is pinned by an exhaustive check rather than by a reference implementation:
over a two-variable ring on a three-element field, `multivariate_gcd.rs` enumerates every candidate
divisor and asserts the defining property — the result divides both inputs, and *every* common
divisor divides the result. That is the property to test, because a GCD is only unique up to a unit
and several candidates share the maximal degree.

### Three routes: two remainder sequences and one modular

`GcdRoute` picks the route. All three return the same value — a reduced GCD is unique once
normalized — but only the first two are the same recursion, differing in what they do to a
pseudo-remainder before the next step. Brown's main path evaluates and interpolates; its
cleanup and fallback can still invoke PRS.

| route | per step | coefficient bound | can refuse |
|---|---|---|---|
| `PrimitivePrs` | divide out the content, which is a recursive GCD | removes content; support and coefficient degree can still grow | no |
| `SubresultantPrs` (default) | divide by `g * h^delta`, one exact division | by a theorem: the entries are subresultants | no |
| `Brown` | evaluate, solve image GCDs, interpolate; PRS cleanup/fallback | image/interpolant degrees depend on the input | **yes** |

`Brown` is reached through `try_gcd_by`, not `gcd_by`. This implementation generates points by
repeated addition of one and therefore enumerates only a prime field, not all elements of an
extension. It also needs **more elements than the degree it interpolates over**, which GF(2)
and GF(3) do not have for most inputs. `FiniteField` carries no characteristic, so `gcd_by` cannot
check either condition and panics rather than guessing; `try_gcd_by` is bounded on `KnownOrder` and
returns `GcdError::ExtensionField`, `GcdError::TooFewPoints` or `GcdError::OrderNotEnumerable`
saying which condition failed. The two sequences never refuse, so `try_gcd_by` is just `gcd_by` for
them.

Collins' subresultant PRS carries `g = lc(a)` and `h = h^(1-delta) * g^delta` across steps, and the
fundamental theorem of subresultants is what makes the division by `g * h^delta` exact. The entries
of the sequence then *are* subresultants — determinants of submatrices of the inputs' Sylvester
matrix. Over finite fields their coefficient *degree* is bounded by determinant expansion;
Hadamard's integer magnitude bound does not measure fixed-width field elements. The primitive
PRS removes content but can still grow support and coefficient degree, paying a recursive GCD
in a smaller ring for each step. Raw pseudo-remainders precede exact scaling and have a separate
size profile.

It needs a pseudo-remainder with **exactly** `delta + 1` powers of the divisor's leading
coefficient, which is what the theorem is stated over. The primitive route's pseudo-remainder
multiplies once per division *step*, and a step that skips a degree leaves the power short —
`x^6 + 1` against `x^2 + 1` takes three steps where `delta + 1` is five — so the two
pseudo-remainders are not interchangeable and the subresultant route has its own.

**The subresultant route is the default on a measured tail, not on a measured median — and not on
the operation count.** #407 took the first timings for either route, and they do not follow the
count. On twenty shapes per field crossing arity, factor size and exponent, the **primitive** route
wins 14–16 of them and the subresultant route 2–3; the subresultant route's typical loss is 10% to
50%.

What decides the default is the other end of the distribution:

| | shape | primitive | subresultant | |
|---|---|---:|---:|---|
| the primitive route's worst | KoalaBear, 4 vars, 10 terms | **1.2561 s** | 0.0020 s | **628x** |
| the subresultant route's worst | KoalaBear, 4 vars, 16 terms | 0.0011 s | **0.0262 s** | 24x |

And on one four-variable shape the primitive route did not finish a single pass in the ~40 minutes
remaining of a 2 400 s run, which is how the first attempt at this sweep was killed mid-table. The
content recursion is a possible explanation, rather than an established causal profile. Both
PRS routes extract contents; subresultant scaling avoids extracting one after every step.
The [intermediate-size study](../research/multivariate-gcd.md#7-intermediate-size-profiles-652)
separates normalized entries, completed raw remainders and recursive call counts. Neither route
has a universal runtime bound established by these timings.

**So `PrimitivePrs` is not merely the reference implementation.** It is 10–50% faster on most
shapes, and `gcd_by(&other, GcdRoute::PrimitivePrs)` is a reasonable choice for a caller who knows
its inputs are ordinary.

**And the same shape repeats one level up with `Brown` (#434): it owns the tail both sequences
lose.** On every shape that defeats a sequence, on every field, Brown's is the fastest of the three
— by **4.3x to 67x** against the better of the other two:

| field | the sequences' worst shape | primitive | subresultant | **Brown** |
|---|---|---:|---:|---:|
| KoalaBear | 4 vars, shared 2, cofactor 6 | **1.3704 s** | 0.0020 s | **0.000459 s** |
| KoalaBear | 3 vars, shared 5, cofactor 5, exp 4 | 0.0025 s | **0.0348 s** | **0.000518 s** |
| BN254 `Fr` | 3 vars, shared 5, cofactor 5, exp 4 | **0.0510 s** | 0.0328 s | **0.003096 s** |

And it loses the median on two fields of three, by up to **5.2x** on the smallest shapes — its cost
is one univariate GCD per evaluation point per level of recursion plus one interpolation, which is
the whole cost on a shape the sequences finish in ten microseconds. So all three routes are fastest
somewhere, and the default is the best route that **always answers**.

The historical sweep at one-minute loads of 9.51 and 2 100.79 found the
`subresultant / brown` ratio agreed on all 40 paired shapes to within 0.06. This observation is
not a general contention guarantee. `gcd_routes` reports ambient load; matched controls and
repeat ranges are needed before interpreting new timing differences.

[`docs/research/multivariate-gcd.md`](../research/multivariate-gcd.md) has the full tables, the
single-repetition caveat on the 628x figure, §5.3's cross-load check, and what the measurement does
not establish — including that the input distribution F4 and FGLM actually hand `gcd` is still
unmeasured, which is why the default is **not** changed to dispatch on the field.

```text
cargo run --release --example gcd_routes
```

`benches/multivariate_gcd.rs` is the criterion regression surface for the same question — four
shapes, one per regime, with the Brown arm probed outside the timed region and not registered where
it refuses, since criterion cannot express "this arm does not apply":

```text
cargo bench --bench multivariate_gcd
```

## Composition

`compose_univariate` substitutes one univariate polynomial per variable, `x_i -> g_i(x_i)`, and
`compose` is the general form, replacing each `x_i` by a polynomial in all `N` variables at once.
Both are simultaneous rather than sequential: a substitution's own variables are not themselves
substituted. `from_univariate(i, &g)` is the lift the univariate form is built on — the same `g`
read as a polynomial in variable `i` alone.

A round of a sponge permutation is exactly this shape: an S-box `x -> x^d` per state word followed
by an affine layer.

```rust
use zeebra::{fields::Zp13, FiniteField, MultivariatePolynomial, Polynomial, UnivariatePolynomial};

let vars = ["x", "y"];
let p: MultivariatePolynomial<2, Zp13> =
    MultivariatePolynomial::parse("x^2*y + 3*x + 2", vars).unwrap();

// x -> x + 1, y -> y^2, written as coefficients in ascending order.
let shift = UnivariatePolynomial::new(&[Zp13::new(1), Zp13::new(1)]);
let square = UnivariatePolynomial::new(&[Zp13::new(0), Zp13::new(0), Zp13::new(1)]);
assert_eq!(
    p.compose_univariate(&[shift, square]),
    MultivariatePolynomial::parse("x^2*y^2 + 2*x*y^2 + y^2 + 3*x + 5", vars).unwrap()
);

// The general form can mix variables: x*y under x -> x + y, y -> x - y is x^2 - y^2.
let product: MultivariatePolynomial<2, Zp13> = MultivariatePolynomial::parse("x*y", vars).unwrap();
let sum = MultivariatePolynomial::parse("x + y", vars).unwrap();
let difference = MultivariatePolynomial::parse("x - y", vars).unwrap();
assert_eq!(
    product.compose(&[sum, difference]),
    MultivariatePolynomial::parse("x^2 - y^2", vars).unwrap()
);
```

Degree grows multiplicatively — `deg(p(g_0, ..., g_{N-1}))` is bounded by the largest
`sum_i e_i * deg(g_i)` over the monomials `x^e` of `p` — so forming the powers `g_i^(e_i)` is where
the work is. They are memoized per variable and built by repeated squaring, which makes a distinct
exponent `e` cost `O(log e)` multiplications and a repeated one cost none. Cancellation is handled
by the same canonical invariant as everything else: a composition that collapses returns the zero
polynomial as no terms at all.


## Factoring Univariate Polynomials
`factorize` returns the monic irreducible factors of a univariate polynomial over a finite field,
with multiplicities, and `is_irreducible` tests a single polynomial:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::{factorize, fields::Zp7, is_irreducible, FiniteField, UnivariatePolynomial};

// x^3 + 6x^2 + 11x + 6 = (x + 1)(x + 2)(x + 3) over GF(7)
let f = UnivariatePolynomial::<Zp7>::new(&[
    Zp7::new(6), Zp7::new(11), Zp7::new(6), Zp7::new(1),
]);

let mut rng = StdRng::seed_from_u64(0);
for (factor, multiplicity) in factorize(&f, &mut rng) {
    assert!(is_irreducible(&factor));
    println!("({})^{}", factor, multiplicity);
}
```

The distinct irreducible factors of each degree are collected with `gcd(f, x^(q^d) - x)`, then
each group of equal-degree factors is separated by Cantor–Zassenhaus splitting. Because
`x^(q^d) - x` is squarefree, that gcd gives the distinct factors whatever the multiplicities in
`f` are — so no squarefree decomposition is needed, and `x^p` in characteristic `p`, whose
derivative vanishes, needs no special handling. Multiplicities are recovered afterwards by
division.

Splitting is randomized, so this takes an rng and the order of the returned factors is
unspecified.

### Modular composition
`compose_mod(f, g, h)` computes `f(g) mod h` by Brent–Kung baby-step/giant-step: the powers
`g^0 … g^(m-1) mod h` for `m ≈ sqrt(deg h)` become the rows of a matrix, one dense matrix product
evaluates every length-`m` block of `f` at `g`, and Horner in `g^m` joins the blocks.
`compose_mod_horner` is the plain Horner reference. When the inner argument is fixed and many outer
polynomials are composed with it — the Frobenius map `p ↦ p^q = p(x^q) mod h` is the case —
`ModularComposer` builds the baby steps once:

```rust
use zeebra::{compose_mod, compose_mod_horner, fields::KoalaBear, FiniteField,
    ModularComposer, UnivariatePolynomial};

let p = |c: &[u64]| UnivariatePolynomial::<KoalaBear>::new(
    &c.iter().map(|&v| KoalaBear::new(v)).collect::<Vec<_>>());
let (f, g, h) = (p(&[1, 2, 3, 4, 5]), p(&[0, 7, 1]), p(&[3, 0, 0, 1]));

assert_eq!(compose_mod(&f, &g, &h), compose_mod_horner(&f, &g, &h));
let composer = ModularComposer::new(&g, &h);
assert_eq!(composer.compose(&f), compose_mod(&f, &g, &h));
```

`factorize` uses it for the Frobenius map `p ↦ p^q` in its distinct-degree loop and in the norm its
equal-degree splitter takes, switching from `pow_mod` once enough applications have accumulated to
repay a composer. On random polynomials of degree 81 and 729 that made whole factorizations 4.5x to
13.9x faster; [`modular-composition.md`](../research/modular-composition.md) has the measurements
and the regime (few applications, narrow field, high degree) where it stays on `pow_mod`.


## Permutation Polynomials
An arithmetization-friendly hash is built from a **power permutation**: Poseidon's S-box is
`x -> x^d`, and that map is a bijection of GF(q) exactly when `gcd(d, q - 1) = 1` — it fixes zero,
and on the multiplicative group, which is cyclic of order `q - 1`, raising to the `d`th power is
injective precisely when `d` is invertible modulo the group order. That inverse is the exponent of
the **compositional inverse**, since `(x^d)^e = x^{de} = x` when `de = 1 (mod q - 1)`. The test, the
enumeration of admissible exponents, and the inverse map are therefore all one piece of arithmetic
modulo `q - 1`.

```rust
use zeebra::{
    fields::{BabyBear, KoalaBear},
    inverse_exponent, is_permutation_exponent, permutation_exponents, FiniteField, KnownOrder,
    PowerPermutation,
};

// KoalaBear, the field the 2026 Poseidon challenges use: p - 1 = 2^24 * 127, which 3 does not
// divide, so the challenge's `alpha = 3` is admissible.
let q = KoalaBear::order_u128().unwrap();
assert!(is_permutation_exponent(3, q));
assert_eq!(inverse_exponent(3, q), Some(1420470955));

// The S-box, and the map an attacker inverts.
let sbox = PowerPermutation::<KoalaBear>::new(3).unwrap();
let x = KoalaBear::new(12345);
assert_eq!(sbox.invert(&sbox.apply(&x)), x);
assert_eq!(sbox.inverse().apply(&x), sbox.invert(&x));

// BabyBear factors differently -- p - 1 = 2^27 * 3 * 5 -- so the cube map is not a permutation
// there, and the smallest S-box exponent above the identity is 7.
let q = BabyBear::order_u128().unwrap();
assert!(!is_permutation_exponent(3, q));
assert_eq!(permutation_exponents(q).find(|&d| d > 1), Some(7));
```

`permutation_exponents` is lazy and yields one representative per distinct map — the admissible
residues in `1..=q-2` — which over a 31-bit field is around `2^31` items, so a caller after the
small exponents an S-box would use should stop early rather than collect.

Exponents are `u128` because `FiniteField::pow` takes a `u128` exponent, so a power map over a
field whose order exceeds that is not expressible in the first place. `PowerPermutation::new`
panics for such a field, and the 254- and 255-bit prime fields are out of reach here.

Deciding whether an *arbitrary* polynomial permutes GF(q) is a much larger subject — Hermite's
criterion, and families such as the Dickson polynomials — and none of it is implemented.
`is_permutation_polynomial` accordingly returns `Option<bool>` and answers only for the shapes whose
answer is immediate: a monomial `c x^d` with `c != 0`, which permutes iff `x^d` does, and an affine
`a x + b`, which permutes every field when `a != 0`. Anything else is `None`, and that is "not
decided here" rather than "not a permutation":

```rust
use zeebra::{fields::Zp7, is_permutation_polynomial, FiniteField, UnivariatePolynomial};

let monomial = |d: usize, c: u64| {
    let mut coefficients = vec![Zp7::new(0); d + 1];
    coefficients[d] = Zp7::new(c);
    UnivariatePolynomial::<Zp7>::new(&coefficients)
};

// gcd(5, 6) = 1, and the leading coefficient only composes a bijection with a bijection.
assert_eq!(is_permutation_polynomial(&monomial(5, 3)), Some(true));
// gcd(3, 6) = 3.
assert_eq!(is_permutation_polynomial(&monomial(3, 1)), Some(false));

// x^3 + x happens to permute GF(7), but establishing that is not in scope.
let f = UnivariatePolynomial::<Zp7>::new(&[Zp7::new(0), Zp7::new(1), Zp7::new(0), Zp7::new(1)]);
assert_eq!(is_permutation_polynomial(&f), None);
```

A cipher's S-box exponent is part of its specification: a different exponent is a different
cryptographic problem, not a variation on the same one. What these utilities are for is a sweep that varies `alpha` deliberately and measures what the
solving degree does.

### Intermediate-size diagnostics

The opt-in `research-work` feature exports `gcd_profile::measure(|| computation)`.
It returns the unchanged answer and a `GcdProfile` whose maxima cover all recursive
calls in that synchronous scope. Normal builds compile out its hooks. Nested
scopes panic, and unwinding resets the thread-local scope.

`prs_entries` observes the initial primitive operands and each subsequent normalized/scaled
entry. `raw_remainders` observes completed pseudo-remainders before content extraction or
exact scaling, including constant remainders where the solver returns immediately.
It does not observe every multiplication temporary inside pseudo-division.
Brown's `brown_images` records accepted scaled images, including images later
discarded when a lower GCD degree is discovered; `brown_interpolants` records
the complete interpolated candidate before primitive-part cleanup. Rejected image
attempts and interpolation construction temporaries are excluded. Brown's PRS
columns therefore describe cleanup/fallback, not image sizes.

Every phase reports its largest polynomial term count and coefficient total degree:
remove the current main variable's exponent from each monomial, sum remaining
exponents in `u64`, and take the maximum. This is neither coefficient bit length
nor simultaneous memory. The two maxima need not occur in the same entry;
`observations=0` distinguishes an unobserved phase from an observed zero polynomial
(whose reported degree is zero). `gcd_calls` and `max_recursion_depth` count recursive
`gcd_by`/Brown `try_gcd_by` entry points (including content recursion), excluding
Brown's private evaluation recursion and univariate Euclid internals.
`content_calls` includes both PRS and Brown content entry points. Fallbacks are
reported separately. The subresultant-derived degree envelope also applies to primitive entries,
which divide the corresponding subresultants. Local bound checks cover initial
inputs and every materialized scaled/primitive next entry of both PRS routes;
raw remainders have no such claim. The `subresultant_*` statistics are named for
the determinant theorem supplying the bound and include checks on primitive
entries as well; they are not counters exclusive to `GcdRoute::SubresultantPrs`.

With `--features research-work`, the ordinary `gcd_routes` sweep prints phase-size
tables from its pre-timing correctness passes. For expensive shapes, isolate a
single route instead:

```sh
cargo build --release --features research-work --example gcd_routes
timeout 10s target/release/examples/gcd_routes --case koalabear 4 4 primitive on
```

Use the actual `$CARGO_TARGET_DIR/release/examples/gcd_routes` path when configuring
an external target directory. `--case FIELD ARITY SHAPE ROUTE MODE` accepts fields
`koalabear|goldilocks|bn254`, arities `2|3|4`, shape indices `0..6`, routes
`primitive|subresultant|brown`, and modes `off|on`. `off` also works without the
feature. Each JSON response retains deterministic input text/digest, full normalized
GCD or typed refusal text, scoped function duration, process RSS and optional
profile. Its input SHA-256 binds characteristic limbs, arity and both canonical
Display polynomials. It is a study identity, not the external corpus digest.
The legacy full sweep still excludes the known over-budget four-variable
shape; per-child external limits protect the single-case campaign instead.
