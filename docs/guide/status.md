# Status: what is implemented

A running record of what Zeebra implements. The short version is in the [README](../../README.md).

- [x] Big Integers
- [x] Integer Factoring
- [x] Finite Field Arithmetic for Large Finite Fields
- [x] Univariate and Multivariate Polynomials over Finite Fields
- [x] Linear Algebra over Finite Fields
- [x] Number-Theoretic Transform (FFT over Finite Fields)
- [x] Grobner Bases
- [x] Polynomial System Solving via Grobner Basis Algorithms
- [x] Sparse Linear Algebra over Finite Fields
- [x] F4 Grobner Bases
- [x] Gebauer-Moller and chain criteria, structured elimination, adaptive linear algebra
- [x] FGLM monomial-order conversion and fallible zero-dimensional solving
- [x] Differential testing of the zero-dimensional pipeline against Singular
- [x] That oracle over an extension field: a differential case names a field rather than a
      characteristic, and the irreducible polynomial the two sides reduce by is asserted to agree
      rather than conventionally shared
- [x] Batched border reduction and adaptive operator storage: 14x on katsura-7's conversion
- [x] 254- and 255-bit prime fields, with F4, FGLM and solving over them end to end
- [x] Two-adic roots of unity without factoring `q - 1`, so the NTT runs over the wide fields
- [x] Batch inversion by Montgomery's trick: the inverse NTT now costs what the forward one does
- [x] Graeffe-transform root finding: one root at degree `3^13` over KoalaBear in 3.1 s, against an
      extrapolated 57 hours for the quadratic finder
- [x] Lenstra's elliptic curve method, with an explicit effort budget that can report the cofactors
      it could not split
- [x] The bivariate resultant's Sylvester determinants in parallel: 92–95% efficiency out to 32
      cores, with the resultant byte-identical at every worker count and the concurrency recorded in
      every `Environment`
- [x] The whole solving pipeline in characteristic two, over GF(2) and GF(2^8), and field equations
      `x^q - x` that make a quotient dimension count base-field points
- [x] Text input and exhaustive enumeration over an extension field, on a settled split between the
      integer embedding `FiniteField::new` and the element index `KnownOrder::element_at`
- [x] A contract for driving external Gröbner engines as subprocesses, which separates "this tool
      cannot represent the input" from "this tool was slower", and refuses to quote a ratio against
      a comparand that could not accept the problem
- [x] Multivariate multiplication that collects as it multiplies, so the live set is bounded by the
      product's size and not by the term-product count: the six-round symbolic build from 57.0 GB
      peak resident to 0.32 GB, 179x, for byte-identical output
- [x] That dense accumulator generalized past two variables, which turned out to pay: 1.3x–5.4x
      over the hashing route at three, four and five variables and 8.4x on a trivariate pair dense
      in two variables and linear in the third, with the box-versus-simplex crossover measured
      rather than argued — and one shape where generalizing the layout *loses*, found the same way
- [x] Multivariate `Add`, `Sub` and `scale` collecting into an operand's own map, so a sum that
      cancels to one term out of 11 476 a side allocates nothing at all where materializing held
      594 KB, and an owned accumulator grows in place
- [x] A cross-library corpus whose ideal equivalence is checked before any timing is published —
      Katsura, Cyclic, random MQ and planted MQ, extensible by a caller's own rungs — with the Katsura indexing and affine-versus-homogenized Cyclic conventions
      resolved against msolve's own distributed input files — now at **two** reference
      characteristics, `2^31 − 1` and `GF(32003)`, each rung frozen at each, because a rung at
      another prime is another ideal and not the same one under a parameter
- [x] The ladder to `katsura-11` and `cyclic-10`, with the quotient dimension **asserted** per rung
      against the published record rather than merely reported: `2^(N−1)` exact at eight consecutive
      Katsura rungs, 70/156/**924** for Cyclic against Björck–Fröberg and Backelin–Fröberg, and the
      cyclic dimension class from Backelin's squarefree criterion — and a **measured ceiling** at
      `cyclic-9`, set by the F4 basis crossing its live-entry budget, which is a bound that crosses
      at the same counter on any machine rather than a wall clock
- [x] Symbolic preprocessing's monomial queue deduplicated on push rather than on pop:
      `fukuoka-mq-III-n20-seed0`'s peak RSS 9.1x lower and its runtime 10% shorter, with the
      symbolic closure checked unchanged batch by batch rather than inferred from the basis
- [x] A published 2 400x conversion gap on a cipher-derived system attributed by measuring the same
      system at three characteristics: this crate's conversion/basis ratio is flat to 12% across a 47-bit range of
      primes where the reference's moves 7.3x, so the gap is the reference's field arithmetic — and
      msolve on this machine is 35x faster than either
- [x] The Sylvester determinant's cost law measured over five matrix orders instead of two: cubic to
      within the measurement above L2 — `2.9953 ± 0.0285`, worst residual 3.7% — and no cache
      cliff, since order 4 374's 153 MB matrix exceeds L3 and still fits the law. The budget guard
      takes the larger of the fitted and cubic laws, because a model that under-predicts authorizes
      a run nobody costed
- [x] Two measured same-machine losses in different subsystems, which is what the comparison was
      for: order conversion ~30x behind msolve, and the basis stage 4.11x behind Singular on random
      MQ — the corpus family closest in shape to a cryptanalytic system
- [x] A competitive board that refuses a ratio against a comparand's own startup floor, measured at
      35.91 ms for Singular, 10.29 ms for msolve and 10.36 ms for Sagebrush from the board's own
      rows — and that states its own roster and counts what its gates excluded, so a run that
      silently lost an engine cannot read as a run that never had it. Each ratio also carries the
      corpus's own **provenance** verdict: a problem with no recorded ideal equivalence is refused
      in the cell rather than omitted, and a ratio resting on a single external engine renders
      `NOT CORROBORATED` beside it (#518)
- [x] The board populated to **five libraries**: 180 measured records over the whole corpus ladder
      x both tasks x Zeebra, Singular 4.4.1, msolve 0.11.0, Groebner.jl 0.10.11 and Sagebrush, one
      row per process under the benchmark lock, all four externals agreeing term-for-term before any
      timing was taken. Of 116 pairs, 89 are disqualified by a startup floor and 19 are ones a
      conclusion may rest on: **13 losses, 1 win**. On random MQ at 10 variables this crate is the
      **slowest of the five** — 348x behind Groebner.jl, 119x behind msolve, 87x behind Sagebrush,
      4.1x behind Singular, every engine agreeing on the answer. And the classical families turn out
      to decide something after all: 15.9x behind Groebner.jl on katsura-7 and 6.2x on cyclic-6,
      where against Singular alone they could decide nothing because Singular was starting up
      through all of it
- [x] Multivariate composition: `x_i -> g_i(x_i)` for univariate `g_i`, and the general form that
      substitutes a polynomial in all `N` variables for each one — so a permutation round can be
      written the way it is defined, with the substituted powers memoized and formed by repeated
      squaring
- [x] Multivariate GCD by recursive primitive PRS, with content, primitive part, the formal partial
      derivative and squarefree decomposition on top of it — the GCD's defining property checked by
      exhaustive enumeration over a small ring rather than against a reference implementation
- [x] Squarefree decomposition in characteristic `p`, where the derivative is blind to every
      multiplicity `p` divides: the invisible part is a `p`-th power, so its root is taken exactly
      and recursed on, and the zero polynomial is the only refusal left
- [x] Collins' subresultant PRS beside the primitive one, which becomes the reference: one exact
      division per Euclidean step rather than a recursive content GCD, with the two routes asserted
      equal exhaustively and the saving stated as an operation count rather than a timing
- [x] Reed-Solomon codes over an FFT domain: encoding, erasure recovery, and a Euclidean
      decoder that verifies its correction rather than returning the nearest codeword
- [x] General-purpose system transforms — affine elimination, specialization with slice solving
      that keeps a slice's emptiness apart from the system's, and reversible variable reordering —
      and generic experiment records, under `grobner::transform` and `grobner::record`

The cryptanalysis research that used to live in `grobner::research` — cipher models, CICO
formulations, a challenge registry and scoreboard, attack cost models — left the crate in #668.
Its entries above are removed; the history is in git at `9532a9a2`.
