# A heap multiply route: ordered output, measured against the caller's sort (#443)

**Measured at:** `b1f016ab` (base `f0013087`), the commit that introduced `MultiplyRoute::Heap`;
the commit after it changes only doc comments in the measured file. The §1 census was taken at
`f0013087` plus a throwaway instrumentation patch that is not committed (described in §1 so it can
be rebuilt).

#443 asked whether a Monagan–Pearce heap multiply earns a seventh route, and asked it as two
separate claims, because only the first is specific to a heap:

1. **Ordered output.** A heap emits the product in monomial order. If callers sort multiply results,
   the heap pays for itself in the sort it removes, so it has to be measured as multiply-then-sort.
2. **No hashing.** The heap hashes nothing during the merge and allocates no cells, so it might fill
   the gap between `Accumulate` and `DenseSimplex` on sparse high-arity pairs, which is where
   `DENSE_MERGE_FACTOR` refuses the dense routes.

**Verdict: both claims fail as reasons to change dispatch.** On the multiply alone the heap is
2.2x–10x slower than `Accumulate` on every shape measured, so the gap claim 2 described does not
exist. Multiply-then-sort does improve on collision-free sparse pairs, by up to 1.9x. But §1 finds
**no production caller that sorts a multiply result**, so nothing is there to collect the saving.
`MultiplyRoute::Heap` and `multiply_sorted` stay reachable, `route()` does not select them, and this
note is the reason, following the precedent of `Materialize` and `Chunked`.

```sh
cargo test --lib sparse_multivariate_multiply
cargo run --release --example multivariate_mul -- heap
```

## 1. Who sorts a product: the census

The method, so it can be rebuilt. `multiply` (the dispatched `*`) recorded an order-independent
fingerprint of every product with more than one term: the term count plus the wrapping sum of
`hash((monomial, coefficient))`. The three ordering sites #443 names then checked their input
against that set: `sorted_terms` (what `normal_form` sorts), `Reducer::new` (the divisor tail
sort), and `leading_term`, which is a max scan rather than a sort but is what a sorted product would
make O(1).

| workload | `*` calls | term-products | `sorted_terms` on a product | `Reducer::new` on a product | `leading_term` on a product |
|---|---:|---:|---:|---:|---:|
| F4, cyclic-6 grevlex | 0 | 0 | 0 / 0 | 0 / 0 | 0 / 584 |
| F4, katsura-7 grevlex | 0 | 0 | 0 / 0 | 0 / 0 | 0 / 367 |
| Buchberger, katsura-5 grevlex | 98 | 1 233 | 0 / 62 | 97 / 811 | 108 / 969 |
| Buchberger, cyclic-5 lex | 2 444 | 33 106 | 0 / 1 233 | 40 425 / 62 072 | 42 328 / 64 732 |
| `solve`, planted 4-variable | 16 | 42 | 0 / 12 | 20 / 64 | 30 / 112 |
| 20 trivariate GCDs | 353 754 | 1.80e8 | 0 / 0 | 0 / 0 | 4 168 / 368 790 |
| 10 trivariate squarefree parts | 322 943 | 6.20e8 | 0 / 0 | 0 / 0 | 3 332 / 354 660 |

How to read it:

- **F4 multiplies nothing through this route.** Its rows are monomial multiples built in
  `grobner::f4::symbolic` with their own indexing. F4 is the production Gröbner path, so claim 1
  has no consumer there.
- **The Buchberger "hits" are not products being sorted.** In every Buchberger and `solve` row the
  term-product count equals the output term count, so each multiply has a one-term operand: these
  are `s_polynomial`'s `monomial * p.scale(..)`. The S-polynomial is the *difference* of two such
  products, which is why `sorted_terms` sees 0 hits. The `Reducer::new` hits are basis elements that
  happen to equal a product `1 · p`, when the S-pair lcm is `p`'s own leading monomial. The divisor
  tail is sorted because it is a basis element, not because it came out of a multiply. A heap would
  remove none of these sorts.
- **The GCD and squarefree paths are where the multiplication is**, 6.2e8 term-products in the
  squarefree row, and they never sort a product. They take a leading term of one in about 1% of
  `leading_term` calls (4 168 of 368 790), and that is an O(n) scan rather than a sort.

So the share of multiply results that a caller immediately sorts is **zero on every workload
measured**. That decides claim 1 before any timing: an ordered multiply can only win where a caller
would otherwise sort, and none does. §2 measures the counterfactual anyway, because #443's
acceptance asks for it and because a future caller that does sort products should know the answer.

## 2. The A/B

KoalaBear, grevlex, one process on core 6 (`taskset -c 6`) under `tools/benchlock.sh`
(START load 2.24, END 1.89, 16 s wall against a 30-minute budget stated up front). Release build
with `RUSTFLAGS` unset, so the ISA floor is the repository's `-C target-cpu=x86-64-v3` from
`.cargo/config.toml`. AMD Threadripper PRO 5995WX. There are four arms per shape, interleaved, with
the arm order rotated each repetition, 7 repetitions each, minimum reported. Medians are in the raw
output and agree to within 10% except where noted. Every arm is checked against `Accumulate`'s
answer, and both sorted arms against the same sorted vector, outside the timing.

- **accumulate**: `MultiplyRoute::Accumulate`, the route `route()` dispatches on every sparse row.
- **heap**: `MultiplyRoute::Heap`: the heap merge, then stored into the term map.
- **acc+sort**: `Accumulate`, then collect and sort descending, which is what `sorted_terms` does.
- **heap sorted**: `multiply_sorted`: the heap's output as a sorted `Vec`, no map at all.

| shape | products | out terms | dispatched | accumulate | heap | heap / acc | acc+sort | heap sorted | sorted / acc+sort |
|---|---:|---:|---|---:|---:|---:|---:|---:|---:|
| N=4, 30×30, e≤20 | 900 | 900 | Accumulate | 9.4 µs | 45.0 µs | 4.79 | 51.0 µs | 35.9 µs | **0.70** |
| N=4, 100×100, e≤20 | 10 000 | 9 959 | Accumulate | 171.5 µs | 1.20 ms | 6.99 | 1.15 ms | 1.00 ms | **0.87** |
| N=4, 300×300, e≤20 | 90 000 | 86 145 | Accumulate | 1.26 ms | 10.41 ms | 8.26 | 9.92 ms | 9.61 ms | 0.97 |
| N=4, 1000×1000, e≤20 | 989 028 | 657 226 | Accumulate | 43.02 ms | 139.04 ms | 3.23 | 118.73 ms | 120.53 ms | 1.02 |
| N=6, 30×30, e≤12 | 900 | 899 | Accumulate | 17.5 µs | 49.7 µs | 2.84 | 60.1 µs | 43.7 µs | **0.73** |
| N=6, 100×100, e≤12 | 10 000 | 9 999 | Accumulate | 223.4 µs | 1.09 ms | 4.89 | 1.11 ms | 1.01 ms | **0.91** |
| N=6, 300×300, e≤12 | 90 000 | 89 936 | Accumulate | 2.54 ms | 13.22 ms | 5.20 | 13.22 ms | 12.00 ms | **0.91** |
| N=6, 1000×1000, e≤12 | 1 000 000 | 991 348 | Accumulate | 92.06 ms | 202.70 ms | 2.20 | 227.17 ms | 144.90 ms | **0.64** |
| N=8, 100×100, e≤8 | 10 000 | 10 000 | Accumulate | 263.1 µs | 1.33 ms | 5.06 | 1.39 ms | 1.24 ms | **0.89** |
| N=8, 1000×1000, e≤8 | 1 000 000 | 999 553 | Accumulate | 103.66 ms | 236.02 ms | 2.28 | 273.15 ms | 169.67 ms | **0.62** |
| N=6, 100×100, e≤2 (colliding) | 8 463 | 5 212 | Accumulate | 215.3 µs | 1.00 ms | 4.66 | 750.7 µs | 967.2 µs | 1.29 |
| N=6, 300×300, e≤2 (colliding) | 61 722 | 12 902 | Accumulate | 1.94 ms | 7.04 ms | 3.64 | 3.40 ms | 7.00 ms | 2.06 |
| N=6, 10×3000, e≤12 (unbalanced) | 29 980 | 29 976 | Accumulate | 743.9 µs | 2.20 ms | 2.95 | 3.76 ms | 1.95 ms | **0.52** |
| N=6, 1×3000 (term multiple) | 2 998 | 2 998 | Accumulate | 64.7 µs | 296.6 µs | 4.58 | 289.7 µs | 271.3 µs | 0.94 |
| N=3 dense simplex deg 12, squared | 207 025 | 2 925 | DenseBox | 1.24 ms | 12.71 ms | 10.24 | 1.41 ms | 12.61 ms | 8.97 |
| N=5 dense simplex deg 4, squared | 15 876 | 1 287 | DenseSimplex | 331.6 µs | 1.24 ms | 3.75 | 435.6 µs | 1.24 ms | 2.84 |

In the dense rows the `accumulate` and `acc+sort` columns are the *dispatched* dense route's
competitor, `Accumulate`, so the dense route itself is faster again. The sorted arms are
`Accumulate`-based because that is the comparison claim 1 makes. The heap loses to both.

### Claim 2: there is no gap

The heap merge is slower than `Accumulate` on **every** row, at least 2.2x and up to 8.3x on the
sparse rows, so it cannot sit between `Accumulate` and the dense routes. Each pop and push walks
`log₂(rows)` levels, and each level is a full `[u32; N]` grevlex comparison, which costs more than
one hash and probe of `MonomialHasher`. Monagan and Pearce get their constant factor from **packed
exponent vectors**, where a monomial comparison is one machine-word compare. Zeebra's `Monomial<N>`
is unpacked, and packing it is a representation change across the crate, not a
multiply route. Their chaining of equal monomials is also not implemented here. It would help only
the colliding rows, which the heap loses by the widest margin anyway.

### Claim 1: real, on collision-free sparse pairs, and nobody collects it

Against multiply-then-sort, the heap's sorted output wins on the collision-free sparse shapes, by
1.1x–1.4x at moderate sizes and 1.6x at the 10⁶-product N ≥ 6 rows. It is best on the unbalanced
10×3000 pair, at 1.9x, because there the heap is 10 entries deep while the sort is over 30 000
terms. It is even at N = 4 and 10⁶ products, where a third of the products collide. It **loses**
wherever products collide heavily: 1.3x–2.1x at e ≤ 2, and 9x on the dense pairs, because the heap
pays a pop per *product* while the sort pays per *output term*. The term multiple, one row, is a
wash at 0.94: the heap's work there is sorting the long operand, which is the same sort.

The improvement is therefore conditional on two things: a caller that sorts the product, and a
product with few collisions. §1 finds the first condition absent everywhere. The one caller shaped
like it, `s_polynomial` feeding `normal_form`, sorts a *difference* of two term multiples. Its
better fix is a merge of two sorted sequences, which is `subtract_shifted` and the division code's
business (#562), not a multiply route.

## 3. What changed, and what would reopen this

- `MultiplyRoute::Heap` and `multiply_sorted` (descending, cancellation-dropping, any
  `MonomialOrder`) in `src/poly/multivariate/sparse_multivariate_multiply.rs`, reachable through
  `multiply_multivariate_unstable` and `multiply_multivariate_sorted_unstable`. `route()` is
  unchanged.
- Differential coverage: the heap is in every all-routes test against `Materialize`, cancellation
  included, and a proptest checks `multiply_sorted` is strictly descending under lex, grlex,
  grevlex, a weighted order and a block order, over every field and at arities 1–6.

Reopen if a caller appears that multiplies and then sorts a sparse, collision-poor product. The
`multiply_sorted` arm above is the figure to beat. Reopen it too if `Monomial<N>` gains a packed
representation, since that changes the heap's per-comparison cost, and the comparison is what
claim 2 lost on.
