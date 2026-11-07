# Sagebrush at `86d9f1c7`: what the engine is, how mature it is, and what reuse would cost

Source study for #266, read at the commit Zeebra measures against:
**`86d9f1c787030752dcaab1ddb8d99cf1b7fa5e1b`**, dated 2026-11-06, cloned by
`tools/external/provision.sh`. Every `path:line` below is relative to the repository root and was
read at that range.

Sagebrush matters disproportionately for one reason: it is the **only permissively licensed
comparand in M25** (`MIT OR Apache-2.0`), so it is the only one whose code Zeebra could lawfully
reuse. That makes the question "is it right?" come before "is it fast?", and §6 before §8.

The adapter is `src/grobner/external/sagebrush.rs`; the driver it goes through is
`tools/external/sagebrush-driver`; what it is like to provision is
`docs/research/external-comparands.md` §5.

---

## 1. There is a Gröbner engine and there is no Gröbner CLI

`engine/` is a 24-member Cargo workspace (`engine/Cargo.toml:1-3`). It builds a `sagebrush` binary
from `engine/cli`, and that crate depends only on `sagebrush-bigint`, `sagebrush-modsym`,
`sagebrush-ap` and `sagebrush-par` (`engine/cli/Cargo.toml:12-15`) — **not on `mpoly`**, where the
Gröbner engine lives, and it exposes no Gröbner entry point.

The engine is a library, and the public prime-field entry point is `engine/mpoly/src/f4.rs:671`:

```rust
pub fn groebner_p(fs: &[QPoly], o: Order, p: u64) -> Result<Vec<QPoly>, String>
```

Hence `tools/external/sagebrush-driver` — ~190 lines of Zeebra's own MIT code that reads an
msolve-format file and calls that function. It is a path dependency on the clone, built with its
own `CARGO_TARGET_DIR`, and it copies no Sagebrush code (§7).

Sizes, for the reuse discussion in §8: `engine/mpoly/src` totals 9310 lines, of which `f4.rs` is
1318, `f4q.rs` 913, `fglm.rs` 622, `sparse.rs` 384, `sigf4.rs` 344, `order.rs` 148, and `lib.rs`
1938.

---

## 2. What the engine actually is: a real F4, with a sugar strategy

It is a genuine F4 — Macaulay-style matrix construction with monomials as columns and a row
echelon — and not a batched Buchberger. `engine/mpoly/src/f4.rs:1-11`:

```rust
//! F4 over GF(p): the pairs of minimal degree (normal strategy) are reduced
//! together. ... become the rows of a matrix with the monomials (decreasing)
//! as columns; ... Pairs are pruned by the Gebauer-Moeller criteria.
```

**That doc line is wrong about the strategy, and the code is the authority.** It is the **sugar**
strategy: `f4.rs:66-67` comments "the sugar degree of each element (the selection strategy)", the
sugar is computed at `:121-122`, and selection takes the minimum of it at `:340`:

```rust
let dmin = self.pairs.iter().map(|q| q.deg).min().unwrap();
```

Under a degree order all pairs of minimal sugar are taken. **Under lex and invlex it additionally
narrows to the single smallest lcm** (`:344-348`), so lex degenerates to Buchberger-like one-pair
steps — a structural fact worth knowing before comparing a lex figure against Zeebra's lex F4,
because the two are not doing the same amount of work per iteration.

**Gebauer–Möller** appears twice: in `F4::update` (`:105-134`) with the chain criterion (`:113`),
the product criterion through `pk.coprime` (`:113`, `:118`), old-pair pruning (`:125-127`) and
deactivation of superseded elements (`:129-133`); and replayed on a finished basis as `gm_pairs`
(`:965-990`) for the over-Q verification.

**Symbolic preprocessing** is `F4::preprocess` (`:154-203`): a worklist over monomials, with
`reducer()` (`:87-101`) choosing a divisor lead by preferring *active* elements and then *fewest
terms*. That is the F4 "simplify" heuristic rather than Faugère's full `Simplify` table. Columns are
sorted decreasing by `key` at `:200-201`.

**The matrix has two representations, chosen by modulus size** at `f4.rs:219`:

| condition | representation | parallel? |
|---|---|---|
| `p < 2^31` | `eliminate31` (`:287-334`) delegating to `engine/arith/src/spelim.rs`, explicitly Faugère–Lachartre (`spelim.rs:1-15`): sparse `Row { cols: Vec<u32>, vals: Vec<u32> }` (`:19-22`), dense `i64` accumulator kept in `[0, p²)` so no division per update (`:90-92`), `Pivots` indexed by column (`:98-101`) | **yes**, past 32 rows |
| `p >= 2^31` | `reduce_rows` (`:209-281`): sparse pivot rows `Vec<(u32, u64)>`, dense `Vec<u64>` accumulator of length `nc`, left-to-right sweep with `Modulus::add/mul` (`:245-260`) | **no, none at all** |

The 31-bit path picks between two elimination strategies with a cost model over an 8-row sample —
`spelim::reduce_auto` (`:341-394`) choosing `Pivots::reduce` (cascading) or `reduce_fl` (true
Faugère–Lachartre, `B' = A⁻¹B` then one dense update per row entry, `:403`) — then `echelonize`
(`:709`) and `back_reduce` (`:776`).

**Interreduction** is `F4::reduced` (`:401-438`): minimalization by divisibility (`:405-410`), then
for degree orders **all tails reduced in one matrix** (`:430`), and for lex a sequential
`interreduce_seq` (`:446-466`) because, `:444-445`, "in lex orders the monomials a matrix reduction
would gather can be far too many". **Lex bases are produced by homogenizing, running DegLex F4,
dehomogenizing and re-reducing** (`f4_p_opt`, `:491-547`).

### 2.1 `f4q.rs` is the interesting one, and the untested one

Not "F4 over Q" naively. `f4q.rs:1-23`:

```rust
//! The pairs, criteria and symbolic preprocessing are F4's (f4.rs), on the
//! leading monomials over Q.  Each matrix is reduced modulo primes below
//! 2^31 instead of over Q, and what F4 needs of it ... is recovered by
//! Chinese remaindering and rational reconstruction, each row over a common
//! denominator, accepted with two primes to spare.
```

A **per-matrix tracer**: the first two primes reduce the whole matrix, the better one fixes the
pivot set, and later primes only redo that (`:10-13`). Entry `groebner_q_f4` at `:427`; it reuses
`f4.rs`'s `F4` struct directly (`:25`). This is the most novel engineering in the tree. It has
**zero `#[test]`s**, and it is the default route over Q (`SB_F4Q != "0"`, `f4.rs:737`).

`f4.rs` also carries a separate *whole-basis* multi-modular path,
`groebner_q_multimodular` (`:750-873`): bases mod primes near 2^31, lucky-prime voting by leading
monomials, CRT plus `ratrecon` (`:708-721`), then verification.

### 2.2 `sigf4.rs` says what it is, which is unusual and useful

`sigf4.rs:27-31`, self-assessed:

```rust
//! Status (Oct 2026): correct (random ideals against Singular, the
//! benchmarks), almost no reductions to zero, but slower than F4: the
//! basis is not interreduced between degrees (F5C) and the pairs, without
//! the product and chain criteria, are many ... the elimination is
//! sequential.  Experimental (SB_SIGF4).
```

Signature-based / MatrixF5-style, with Koszul syzygies and a rewrite criterion
(`:88-102`, `:172-182`) but **no product or chain criteria** (`:336-337`). Homogeneous only,
`p < 2^31`, degrevlex or deglex; gated behind `SB_SIGF4` (`f4.rs:484`), and its result still goes
through `F4::reduced` (`f4.rs:595-607`). **Zero `#[test]`s**, and the validation "against Singular"
the comment claims has no corresponding test, script or recorded output anywhere in the tree.

This bears directly on #223, which declined the signature-based direction for Zeebra on three
independent legs. Sagebrush is an independent implementation reaching the **same conclusion from
the inside** — slower than F4 in practice, for reasons it names. #266's remit is the implementation
*cost* question, and the answer here is that a careful 344-line signature F4 by a competent author
still lost to its own F4. That is corroboration of #223's decline, not a reopening of it.

---

## 3. Monomial representation: packed exponents with a guard bit

`engine/mpoly/src/order.rs`, 148 lines, the single highest value-per-line file in the tree.

`Packing { n: usize, bits: u32 }` (`:42-45`) puts all `n` exponents in one `u64` with **variable 0
in the highest field** (`:58-60`):

```rust
pub fn shift(&self, i: usize) -> u32 { (self.n - 1 - i) as u32 * self.bits }
pub fn mask(&self) -> u64 { if self.bits >= 64 { !0 } else { (1u64 << self.bits) - 1 } }
```

Because variable 0 is most significant, **a plain unsigned word comparison is a lex comparison** —
which is both the design's elegance and its trap (§4).

`bits` is **dynamic**, not fixed: `f4::bits_range` (`f4.rs:660-666`) starts at
`max(bits_for(maxdeg) + 2, min(8, max))` and caps at `64 / (n + extra)` with `extra = 1` for lex.
`ZPoly` states the invariant `n * bits <= 64` (`lib.rs:100-101`), and after lex dehomogenization the
packing is forced to `bits = min(64/n, 32)` (`f4.rs:519`).

**The top bit of every field is a guard bit** (`order.rs:69-72`), which makes divisibility a
branchless fieldwise compare — `f4.rs:76-79`:

```rust
((b | self.guard) - a) & self.guard == self.guard
```

So the usable exponent range per variable is `2^(bits-1)`, not `2^bits`. That is where the
adapter's `MAX_VARIABLES = 32` comes from: at `n > 32`, `64/n` leaves one bit, which is the guard.

`key(Order, word) -> u128` (`:104-125`) turns each order into a sortable integer:

| order | key |
|---|---|
| `Lex` | `w as u128` — the word already compares correctly |
| `DegLex` | `(degree(w) << 64) \| w` |
| `DegRevLex` | `(degree(w) << 64) \| low`, with `low` built by **complementing each exponent (`mask - exp`) and re-laying the fields in reversed order**, so the *last* variable becomes most significant (`:108-116`) |
| `InvLex` | fields re-laid reversed, uncomplemented (`:117-123`) |

**Degrevlex as a pure key transform — degree first, then "smaller last exponent wins" via
complement plus field reversal — is the one idea here Zeebra should look at**, and it is the same
idea Groebner.jl arrives at independently with a complemented degree lane
(`docs/research/groebner-jl-implementation.md` §2.4). Two unrelated implementations converging on it
is the strongest evidence available that it is the right representation.

**Overflow** is detected as `x & guard != 0` after a word addition (eleven sites, e.g.
`f4.rs:168-170`, `:362-364`, `:509-511`) and propagates as the unit error `sparse::Overflow`. The
retry loop **doubles `bits`, capped at `maxb`** (`groebner_p_opt`, `:679-704`):

```rust
Err(Overflow) => {
    ...
    if bits == maxb { return Err("exponents too large to pack".into()); }
    bits = (bits * 2).min(maxb)
}
```

There is **no fallback to a representation wider than one word**: past `64/n` bits the computation
fails with a string error. `in_ideal` softens this to `Ok(false)` — "not certified" — at
`f4q.rs:506-508`.

---

## 4. The trap the adapter is written around

**Terms are stored in decreasing lex order of the packed word whatever the monomial order is**,
because the word comparison *is* a lex comparison (§3). So **for degrevlex `exps[0]` is not the
leading term.** On the provisioning smoke system the second basis element stores as
`x*z + … + z^4 + …`, whose degrevlex leading monomial is `z^4`.

Taking the first term yields a plausible-looking and entirely wrong leading-monomial list, and
nothing announces it. The first version of the driver did exactly that, and only the four-way
agreement caught it; it now uses the public `Packing::key(o, w)`
(`tools/external/sagebrush-driver/src/main.rs`, `leading_word`), and the adapter reads the driver's
`--- leading monomials ---` section rather than any first term.

---

## 5. Coefficients, fields, and the real ceiling

`engine/bigint/src/nmod.rs:1`:

```rust
//! Arithmetic modulo a word-size integer n (2 <= n < 2^64).
```

**Barrett-style, not Montgomery**: `nmod.rs:3-8` cites Möller–Granlund's "Improved division by
invariant integers", Algorithm 4 — a normalized precomputed reciprocal (`:20-26`) and a 2-by-1
division in `reduce_wide` (`:30-48`). `mul` widens to `u128` then reduces (`:90-93`); `add`/`sub`
are branch-free conditional subtracts (`:96-120`); no `%` on the hot path. Shoup's trick for fixed
multipliers (`:174-196`) is documented valid only for `n < 2^63` (`:8`, `:179`).

Coefficients are stored as `Coeffs::Small(Vec<i64>)` or `Coeffs::Big(Vec<BigInt>)`
(`lib.rs:48-51`), demoting to `Small` only when every coefficient fits `i64` (`:84-93`).

### 5.1 The ceiling is 2^62, it is checked, and the driver is on the wrong side of the check

The provisioning record warned that "the representation above 2^63 is not obviously sound"
(`external-comparands.md` §5.3). The source is more precise and the real boundary is lower:

`engine/mpoly/src/lib.rs:1552-1554`:

```rust
if pm < 2 || pm >= 1 << 62 {
    return Err("the modulus must be in [2, 2^62)".into());
}
```

mirrored in the Python front end at `lib/_sage_mpoly.py:398-400`, and corroborated by
`sparse.rs:5` and `:25` documenting `Fp` as "GF(p), p < 2^62" — with `Fp::add` a bare `a + b` plus
one conditional subtract (`:57-63`), which overflows `u64` above 2^63.

Above 2^63 the `i64` storage is unsound two independent ways: `ZPoly::reduce_mod` (`lib.rs:1111`)
does `c.rem_euclid(p as i64)`, and `p as i64` is **negative** there, so the modulus silently
becomes `2^64 - p`; and the big branch does `.to_i64().unwrap()` (`:1124`), which **panics** for a
residue above `i64::MAX`. Same bug shape in `gcd::reduce` (`gcd.rs:107`).

**The gate sits on `call()`, which `f4::groebner_p` does not go through.** So the driver — and
therefore the adapter — bypasses Sagebrush's own enforcement, and past 2^62 would get a wrong
answer or a panic rather than that clean `Err`. That is why
`sagebrush::MAX_CHARACTERISTIC = 1 << 62` is a constant in the adapter: **it enforces Sagebrush's
bound on Sagebrush's behalf.** `p = 2^61 - 1` is comfortably inside it and sound.

### 5.1.1 There are two ceilings, not one, and the second is a trap for whoever extends the driver

`MAX_CHARACTERISTIC` is the **basis** bound. `fglm.rs:329` caps the FGLM route at **`p < 2^31`** —
an eighth of it. That narrower bound went live with #315, which gave the driver an FGLM route, and
the adapter declares it as `sagebrush::FGLM_MAX_CHARACTERISTIC` against
`Task::LexBasisByConversion` alone.

**And it declines softly, which is the part that will bite.** `fglm.rs:329` is

```rust
if n == 0 || (p > 0 && p >= 1 << 31) {
    return Ok(None);
}
```

`Ok(None)` — not an `Err`. A caller that reads `None` as "there is no lex basis" rather than "I
declined to compute one" has turned a capability gap into a mathematical claim. The same `None` is
returned for `n == 0`, so the signal does not even distinguish *why* — and it is also what
`fglm_p` returns for an ideal that is genuinely **not zero-dimensional**, which is a real answer.
The driver therefore checks the characteristic itself before calling, exactly as the adapter checks
the basis bound on Sagebrush's behalf (§5.1); only once that check has passed can `None` be read as
the zero-dimensionality condition, which is what the driver reports it as.

Declaring only the basis bound then would be worse than a build error. A sweep would accept a
`LexBasisByConversion` at, say `2^40`, hand it to a route that cannot represent it, and record
whatever the run did inside its wall limit — a [`LimitStop`] for what is a **capability gap**. A
limit stop is timing-adjacent: it licenses "> 600 s" in a table. A capability gap licenses nothing.
Conflating them is the single distinction `contract.rs` exists to maintain.

msolve has the same shape with worse consequences — basis below `2^31`, eliminant below
`1515531529`, and above the second its sparse-FGLM failure is laundered into the genericity signal
and reaches a retry loop with no exit (`docs/research/msolve-implementation.md`). **Groebner.jl,
measured, has no task-specific ceiling at all**: its lex route is the same F4 under a different
ordering, and it returns the same basis and the same quotient dimension at every prime the basis
route accepts, up to `2^64 - 59`. One constant is correct for it; two are needed here.

### 5.2 Nothing in Rust checks that the modulus is prime

`Modulus::new` asserts only `n >= 2` (`nmod.rs:21`). A deterministic 64-bit Miller–Rabin exists
(`nmod.rs:200-230`, wrapped as `gcd::is_prime_u64` at `gcd.rs:41`) and is used only for prime
*generation*. With a composite modulus, F4 panics at the first non-invertible leading coefficient —
`md.inv(...).unwrap()` at `f4.rs:269`, `:531`, `:588`, `sigf4.rs:124`. Primality is enforced only in
the Python layer (`lib/_sage_mpoly.py:229-231`). Zeebra's adapter is safe here because a
`FieldSpec` comes from a Zeebra prime field, but a harness that ever synthesized a `FieldSpec` by
hand would hit a process abort rather than an error.

### 5.3 What the engine exposes, and what it does not

| capability | in Rust? | where |
|---|---|---|
| degrevlex / deglex basis mod p | **yes** | `f4::groebner_p` (`f4.rs:671`) |
| lex basis | **yes**, two routes | `f4_p_opt` by homogenize → DegLex → dehomogenize (`f4.rs:491-547`); `fglm::groebner_fglm` (`fglm.rs:325`), capped at `p < 2^31` by `:329`, and the default for lex through `call()` (`lib.rs:1661`) |
| FGLM order change | **yes** | `fglm::fglm_p` (`fglm.rs:60`) |
| quotient dimension | **computed, not exposed** | `let d = stair.len();` (`fglm.rs:97`) is internal; only the boolean `zero_dimensional` (`:33`) is public. `vector_space_dimension` is Python (`lib/_sage_mpoly.py:4028`) |
| univariate eliminant | **no** | `elimination_ideal` is Python (`:4083`) and works by taking a lex basis |
| finite-field solutions | **no** | `grep -i variety` over `engine/mpoly/**.rs` is **zero hits**; `variety` is Python (`:4184`) |

So the Rust engine is a **Gröbner engine plus an FGLM order change**, and everything above that —
dimension, elimination, varieties, radicals — is a ~5000-line Python layer.

**Two consequences for the task taxonomy.** First, `LexBasis`, `LexBasisByConversion` and a
quotient dimension were things *Sagebrush* could do and the *driver* could not, so the adapter's
refusals were the driver's limits and not the engine's; #315 closed that gap, and
`LexBasisByConversion` now has a second comparand beside Singular. Second, **Sagebrush confirms that no M25 comparand
enumerates finite-field solutions**: msolve returns a parametrization
(`external-comparands.md` §3.5), Singular's `solve` is numerical, Groebner.jl has no solver
(`groebner-jl-implementation.md` §5.4), and Sagebrush has no variety in Rust.
`OneFiniteFieldSolution` and `AllFiniteFieldSolutions` have **no external comparand at any
characteristic** — a first-class result for the competitive report.

---

## 6. Maturity: the verdict #266 asks for

### 6.1 The structural case, which is weak

| fact | evidence |
|---|---|
| **Five weeks old.** First commit 2026-10-02, HEAD 2026-11-06, 6864 commits between — extremely active, and young. | `git log` |
| **Nothing is versioned.** All 24 `engine/*/Cargo.toml` are `version = "0.1.0"`; the 34 git tags are all product-level (`v*`, `py-v*`, `mcp-v*`) with **no crate or engine tag**; nothing is on crates.io. The pin is a commit SHA because there is nothing else to pin to. | `engine/mpoly/Cargo.toml:3`; `git tag` |
| **Six tests on the F4 path.** `f4.rs` carries `small_q` (`:1209`), `lex_elimination` (`:1217`), `signature_path_matches` (`:1226`), `f4_over_q` (`:1245`), `verify_rejects` (`:1270`), `cyclic4_p` (`:1304`) — for 1318 lines. | — |
| **Zero tests** in `f4q.rs` (913 lines, the default route over Q), `sigf4.rs` and `certify.rs`. | — |
| **The one integration test is not a correctness test.** `engine/mpoly/tests/` holds exactly `f4_poll_gap.rs`, which runs cyclic-7/8 mod 32003 and asserts only `poll <= 250_000_000` ns (`:58`). It never checks the basis — only `g.len()` in an `eprintln!` (`:54`). | — |
| **The oracle trees barely touch Gröbner bases.** `sage-tests/` has 267 entries and **two** mention `groebner_basis`, both two-variable toys; `magma-tests/` has 107 entries and `grep -li groebner` returns **zero**; `conformance/` is MicroPython language conformance, not algebra. There is no committed oracle run on cyclic-n or katsura-n, so nothing in the repository exercises matrix elimination, the lucky-prime voting, the `f4q` tracer, or `sigf4` against an external answer. | — |
| **The claimed Singular validation of `sigf4` does not exist** in the tree. | `sigf4.rs:28` |

Two things that are genuinely good and should be said: `TODO`, `FIXME`, `unimplemented!`, `todo!`
and `panic!(` are **all absent** from `f4.rs`, `f4q.rs` and `sigf4.rs` — unusual and clean — and the
code is densely commented and literature-cited (Faugère; Gebauer–Möller; Faugère–Lachartre;
Möller–Granlund; Arnold; Idrees–Pfister–Steidel; the Eder–Faugère survey). `verify_rejects`
(`f4.rs:1270`) is a real negative test: it rejects a perturbed coefficient, a dropped element and
the raw generators, under both `SB_VQ_CERT=1` and `=0`.

What is there instead of stubs is **unchecked unwrapping**: 33 `.unwrap()` in `f4.rs`, 12 in
`f4q.rs`. The ones that turn a bad input into a process abort rather than an error are
`f4.rs:269`, `:531`, `:588` (non-invertible lead on a composite modulus, §5.2), `f4.rs:784` (two
stacked unwraps on a denominator inside the prime loop) and `lib.rs:1124` (§5.1).

### 6.2 The empirical case, which is now good

`tests/external_comparands.rs` checks Sagebrush against Zeebra **term for term, every coefficient
included** — strictly stronger than the `Invariants` comparison the contract uses, because a reduced
Gröbner basis is unique given the ideal and the order. It agrees on:

| instance | note |
|---|---|
| the reference smoke system over GF(2^30+3) | the four-way agreement system; `vdim = 12` |
| katsura-4, -5, -6, -7 | every Katsura rung on the corpus ladder, digests asserted against the frozen ones |
| cyclic-4, -5, -6 | every Cyclic rung; **cyclic-4 is positive-dimensional**, so no quotient dimension exists and the check is on the basis alone |
| katsura-4 over GF(4611624995532046337) | a 62-bit prime, where **neither msolve nor Singular can represent the input** |
| a 14-variable system containing both `x1` and `x10` | the prefix-collision rung (§4 of the Groebner.jl study); a misread would collapse the ideal to `<1>` |

**Ten distinct instances compared term for term, three families, two characteristics**, where the
provisioning record had one. Across the full eighteen-rung ladder the adapter additionally
*completed* the six MQ rungs and three Poseidon rungs — including both fourteen-variable MQ rungs,
with **no** `exponents too large to pack` — and cleanly refused both Anemoi rungs, whose field is
above its 2^62 gate. One run in that sweep stopped at the wall limit, which is the expected
outcome at the top of the ladder and not a result.

The MQ and Poseidon completions are *not* agreement evidence: the live test has no compiled Zeebra
oracle for those families, so what they establish is that the adapter drives them end to end and
that the status taxonomy holds, not that the answers are right.

### 6.3 The verdict

**Sagebrush's F4 is correct wherever it has been checked, and its timings should carry a maturity
caveat rather than be treated as a baseline.** The two halves of that sentence are both load-bearing.

The empirical case has moved far enough that "do not quote it" is no longer the right instruction —
eight-instance term-for-term agreement with an independent implementation, including a
positive-dimensional ideal and a characteristic no other comparand can reach, is real evidence. What
has not moved is §6.1: there is no release, no version, no oracle coverage of any system large
enough to exercise the elimination, and the default route over Q is untested. A regression between
this commit and any other would be invisible to the repository's own test suite.

So, concretely, for the M25 results table:

* **Report Sagebrush's rows, with the commit SHA and a maturity footnote.** Dropping them would
  discard the only permissively licensed data point and the only corroboration available above
  2^31.
* **Do not make it the denominator of a headline speedup.** A baseline should be something with a
  release and a regression suite; Singular and msolve are.
* **Any instance where it disagrees is reported, not dropped.** Across every instance tried — ten
  compared term for term, sixteen of eighteen ladder rungs driven end to end — **it has not
  disagreed once.**
* **Its 64-bit rows rest on two implementations agreeing** (it and Groebner.jl, with Zeebra as the
  third party) because msolve and Singular stop at 2^31. That is the weakest evidence this module
  produces and must be labelled.

---

## 7. Licensing: reuse is permitted, and would cost three specific things

`NOTICE.md:1-13`:

```markdown
# Sagebrush: licensing notice

Copyright (c) 2026 SageMath, Inc.

Sagebrush is licensed under either of

- the Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE)), or
- the MIT license ([LICENSE-MIT](LICENSE-MIT)),

at your option.
```

`engine/mpoly/Cargo.toml:5` is `license = "MIT OR Apache-2.0"`; `LICENSE-MIT:3` is
`Copyright (c) 2026 SageMath, Inc.`. And `NOTICE.md:16-18` disclaims GPL ancestry:

```
Nothing in Sagebrush
is derived from GPL software: PARI, Sage, Magma and FLINT are used only from
the outside, as oracles in tests and as benchmarks.
```

Two caveats, neither touching `engine/mpoly`: `NOTICE.md:676-690` records PSAGE (GPLv3+) files that
"may be ported to Sagebrush with the copyright holder's permission", relicensed `MIT OR
Apache-2.0`, scoped to `engine/hmf/` and `engine/modsym/`; and `engine/flint/` is bindings to
LGPL-3.0 FLINT (`NOTICE.md:815`). **A reuse that touched only `mpoly`, `arith` or `bigint` is clear
of both.**

### 7.1 Nothing is reused today

The driver calls `sagebrush_mpoly::f4::groebner_p` across a crate boundary and copies no code, so
`docs/research/external-provenance-policy.md` §8.1's notice obligation — which applies to *copied*
code — is not engaged. The clone lives in the provisioning prefix and is not committed; the only
Sagebrush-derived artefact in this repository is the pinned SHA in `tools/external/provision.sh`.

### 7.2 What attribution would require, if something were copied

Groebner.jl is the worked example of a licence-compliant adaptation — a named upstream, a named
licence, and an enumerated list of what was taken, in the first fifteen lines of its entry point
(`docs/research/groebner-jl-implementation.md` §1). Zeebra cannot do that for a GPL upstream,
because the result would be GPL. **For Sagebrush it is straightforward**, because the licence is
permissive and Zeebra may simply elect MIT (policy §8.2) — which is what Zeebra already is, so
Apache-2.0's extra `NOTICE` machinery never engages.

The obligation then reduces to three things, and **all three are required together**:

1. **SageMath, Inc.'s copyright notice and the MIT permission notice travel with the code** —
   a module header naming the origin, plus the full MIT text where a recipient of the *crate* will
   find it. Zeebra's own `LICENSE-MIT` is Zeebra's copyright, not SageMath's, so a second notice is
   needed: `THIRD-PARTY-NOTICES` is the direction policy §8.3 recommends.
2. **The notice ships in the package, not just the repository** — included by `Cargo.toml`'s
   `include`/`exclude` and referenced from the source, the way Arkworks lists its licence files.
3. **Provenance in the source**, in policy §9's format: repository, SHA, `path:line`, access date,
   and what was changed.

And one thing that is *not* sufficient: **a citation in `docs/research/` is documentation, not a
licence notice.** This file satisfies §9; it does not satisfy the licence. Both are required.

### 7.3 The maintenance cost, which is the real argument against

A copied kernel diverges from upstream silently and has **no version to bump** — §6.1's "every
crate is 0.1.0" is exactly this problem. Zeebra's standing preference is to implement and then
measure the in-crate option before taking a dependency, and that preference applies with full force
to taking a *copy*, which is a dependency with none of the tooling. The honest reading of §8 below
is that Sagebrush's value here is as a **design reference that happens to also be legally
copyable**, and that the right use of the permission is to not need it.

---

## 8. Which components could be reused, with the Zeebra measurement that would justify it

Ordered by value per line, and every entry names what would settle it. **None of these is
recommended on the strength of looking efficient.** The premise correction first, because it
reorders the list: M16's "elimination is 65–88% of F4 runtime" is obsolete.
`docs/MILESTONE-F4-OPTIMIZATION.md` §8.5 measures elimination at **7–22%**, with the cost now in
interreduction (28.71 ms of katsura-7 grlex's 46.72, **61%**) and matrix construction (9.33 of
katsura-6 lex's 19.53, **48%**). **#269's title still cites 65–88% and its premise needs
replacing**, and two of the three candidates below would otherwise have been aimed at the wrong
stage.

### 8.1 `order.rs` — the packed monomial with a guard bit (148 lines)

**The one worth looking at.** Self-contained, `std`-only, no coupling to anything else in the tree.
It delivers two things Zeebra's `[u32; N]` (`src/poly/multivariate/monomial.rs:15-19`) does not: a
whole monomial in one `u64` for `n <= 32`, and `key(DegRevLex, w)` as a sortable integer so a
degree-order comparison is one `u128` compare instead of an array walk. Groebner.jl reaches the same
design independently (§3), which is the strongest available evidence it is right.

* **Confirms it:** `interreduction` falls on katsura-7 grlex (28.71 ms of 46.72) and grevlex (16.90
  of 32.13) — the largest remaining cost — and `symbolic` falls on the lex instances. Instrument
  with `examples/f4_profile recommended`, which already reports those columns.
* **Refutes it:** no measurable change, i.e. LLVM already hoists the comparison work for a fully
  unrolled `N = 7` array. **A microbenchmark of `MonomialOrder::cmp` is the five-minute version and
  must come first**, because `Monomial` is serialized (`monomial.rs:17`) and changing it is a format
  change.
* **Copy or implement?** **Implement.** It is 148 lines of ideas, Zeebra's exponent type and
  variable-count regime differ, and §3's overflow story — doubling `bits` and then *failing*, with
  no wider fallback — is not a contract Zeebra should inherit. Taking the idea costs a citation
  (§7.2 item 3, which this file is); taking the code costs all three obligations plus §7.3.

### 8.2 `engine/arith/src/spelim.rs` — Faugère–Lachartre sparse elimination (1035 lines)

Standalone, knows nothing about polynomials, and genuinely a drop-in linear-algebra core:
`Row`, `Pivots`, `reduce`, `reduce_fl`, `reduce_auto`, `echelonize`, `back_reduce`. Its one external
coupling is `SB_F4_DEBUG` at `:386`.

**And its headroom in Zeebra is capped at 7–22%.** §8.5 is explicit that M16's two
elimination-targeted optimizations already worked well enough to stop elimination being the problem.
A drop-in that halved it would buy at most 1.12x overall on katsura-7 grlex.

* **Would make it worth revisiting:** elimination returning above ~30% of total on some instance,
  which succeeding at §8.1 would *not* cause (it targets interreduction) but which a much larger
  corpus might.
* **Measurement:** the `elimination` column. If it stays single- to low-double-digit percent, the
  answer is no however good the routine is.
* **Also note** `reduce_auto` branches on `is_x86_feature_detected!("avx2")` (`spelim.rs:381-384`),
  so the same input can take a different route on different hardware — a property to pin before
  measuring, never to inherit silently.

### 8.3 `nmod.rs` — the Möller–Granlund modular reciprocal (360 lines)

Dependency-free GF(p) with no hardware division. Zeebra already has its own prime-field layer with
a `-C target-cpu=x86-64-v3` floor, and §8.5 leaves no stage where scalar modular arithmetic is the
bottleneck.

* **Measurement that would change this:** a microbenchmark of Zeebra's `PrimeFieldElement64`
  multiply against this reciprocal at Zeebra's actual primes — Goldilocks and its 62-bit prime. **The arithmetic may settle it before the benchmark does:** Shoup's trick here is
  documented valid only below 2^63 (`nmod.rs:8`), and Goldilocks' structure is exactly what
  Zeebra's existing reduction exploits, so a generic reciprocal is unlikely to beat it.
* **Verdict: no**, and for a reason that is a fact about Zeebra's fields rather than about this
  code.

### 8.4 `f4q.rs` — the per-matrix multi-modular tracer (913 lines)

The most novel engineering in the tree, and **not applicable**: it exists to compute over **Q**,
and Zeebra computes over finite fields. There is no multi-modular loop to amortize it over.

* **Measurement that would make it relevant:** none exists, because the capability it serves does
  not. If Zeebra ever acquires a characteristic-0 path, re-read this file first — and note then
  that it has **zero tests** (§6.1), so it would be a design reference and not a source.

### 8.5 `sigf4.rs` — the signature-based path (344 lines)

**Do not reuse, and the reason is #223 rather than the licence.** #223 declined the
signature-based direction on three independent legs, and §2.2 is an independent implementation
reporting the same outcome from the inside: slower than its own F4, non-interreduced between
degrees, sequential elimination, no product or chain criteria. Policy §5.3 reached the same
conclusion — "read it, measure the implementation cost, and copy nothing" — and this reading
confirms it.

* **The implementation-cost answer #266 asked for:** 344 lines, including Koszul syzygies and a
  rewrite criterion, is what a careful signature F4 costs — and it still lost. That is the useful
  number, and it argues against the feature rather than for porting it.

### 8.6 `fglm.rs` — the FGLM order change (622 lines)

Zeebra already has FGLM (`src/grobner/fglm/`). The transferable observation is not the code but a
capability gap in the *driver*: Sagebrush's FGLM is the default lex route through `call()`
(`lib.rs:1661`), which the driver bypasses — so until #315 the driver called `groebner_fglm`
nowhere and `LexBasisByConversion` had only Singular in its column. The driver now calls it
directly, under `--route fglm`.

---

## 9. Follow-ups this study identified

1. **#315 — extend `tools/external/sagebrush-driver` to the orders and tasks the engine already has.
   Done.** `fglm::groebner_fglm` (`fglm.rs:325`) and the lex route in `f4_p_opt` (`f4.rs:491-547`)
   both existed and the driver exposed neither, so the adapter refused `LexBasis`,
   `LexBasisByConversion` and every non-degrevlex order. The driver now takes `--order` and
   `--route`, so `LexBasisByConversion` has a second comparand beside Singular — the one task where
   a second opinion is most valuable, because the two routes to a lex basis have different
   complexity. It also reports a `#quotient dimension:`, which raises the `Invariants` overlap
   against Zeebra from two to three; that number is the driver's own count of the standard
   monomials rather than Sagebrush's internal `stair.len()`, which stays unexposed, and being an
   independent computation it is a real third invariant rather than a restatement.
2. **#316 — add a `RunFailure` variant for a hostile environment.** `src/grobner/external/sagebrush.rs`
   must refuse to run when an `SB_*` switch is inherited, because `Invocation` can set a child's
   variable but not clear one, and those switches are truthy-if-set. The closest existing variant is
   `Reported`, which `contract.rs` explicitly asks an adapter not to overload — so this is the
   "say so rather than overloading" case, said.
3. **#269 — correct its premise.** Its title cites M16's obsolete 65–88% elimination figure;
   `MILESTONE-F4-OPTIMIZATION.md` §8.5 measures 7–22%, with interreduction at 61% and matrix
   construction at 48%. Whatever #269 becomes, it should be aimed at those.
4. **#317 — benchmark the two packed-monomial hypotheses together.** §8.1 here and
   `groebner-jl-implementation.md` §6.2–6.3 are the same idea reached from two independent
   codebases; they should be one experiment, and the microbenchmark of `MonomialOrder::cmp` should
   gate it.
5. **#329 — echo the generators from the driver**, so the adapter can check what it read on every
   run rather than relying on one behavioural test. The driver already self-documents the
   characteristic, the variable order and the monomial order, and the adapter already checks all
   three as `SelfInconsistent`; the generators are the one input fact not covered. This is the
   `x1`/`x10` class of hazard, which **cross-engine agreement cannot detect** — every engine is
   handed the same bytes, so a misread is identical everywhere and four engines agree on the same
   wrong ideal. The driver is verified clean at fourteen variables (it splits on the explicit `*`
   and `^` separators and matches each name whole), and the corpus's `mq-random-14` and
   `mq-planted-14` rungs make the hazard live rather than hypothetical.
6. **#337 — the msolve adapter's corpus agreement test panics on a rung it has no instantiation
   for**, and CI cannot see it because the test returns early when msolve is absent. Not this
   study's subject, but found by it: a test whose skip is indistinguishable from its pass will
   drift again.
