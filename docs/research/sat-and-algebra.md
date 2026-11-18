# SAT and algebra: baseline yes, backend won't-do, one hybrid deferred

Decision record for [#220](https://github.com/mfaulk/zeebra/issues/220) (G3, child of #196), in the
form of [`wiedemann-krylov.md`](wiedemann-krylov.md) (#58). The issue's point was to keep three
very different answers to "does SAT belong in Zeebra?" apart, because the literature on SAT versus
algebraic cryptanalysis mostly does not. Each is closed or deferred here, with the measurement it
rests on.

| option | decision | why, in one line |
|---|---|---|
| 1. SAT as a **baseline** (kissat as an external process) | **Adopted as an oracle**, nothing to build | `tools/external/provision-sat.sh` and `examples/sat_algebra.rs` already run it, the same way msolve and Singular are run |
| 2. SAT as a **backend** (ANF→CNF, dispatch, lift the model) | **Won't do.** Policy decides it on its own; the measurements agree | the crate ships no C dependency and no linked solver (§7); the CNF throws away the XOR structure F4 is built on (§2), and the XOR engine SAT uses to get it back is 55x slower than Zeebra's on the same matrices (§3) |
| 3. **Hybrid**: algebra before SAT, or SAT-style learning inside F4 | **Preprocessing: deferred**, with a measured trigger (§4). **Learning in F4: won't do** (§5) | affine elimination before kissat won on 13 of 15 instances (§4), but the hybrid belongs with whoever runs SAT, not in this crate; a zero reduction has no CDCL-style explanation, and the one it does have is a signature, which M31 already owns |

**Measured at:** `e6b04c24` (§2 clause counts, §3 GF(2) replay) and `60c50d7a` (§4 preprocessing;
the only change between the two is in `preprocess`'s reporting of an F4 refusal). Both are
tagged (`measured/220-sat-replay`, `measured/220-sat-preprocess`) so they survive the squash merge. Raw outputs, with
`uptime` before and after each run, are in [`research/sat-and-algebra/`](../../research/sat-and-algebra/).
One shared 128-thread machine with other work on it (load average 2–4 on 128 hardware threads
throughout), unpinned, `--release` (fat LTO, `target-cpu=x86-64-v3`). Timings are secondary here and
every conclusion below is a ratio of one or two orders of magnitude; read nothing into a difference
under about 30%.

**External versions, exactly:** kissat 4.0.4 (tag `rel-4.0.4`, commit
`8af8e56f174b778aef3aa45af9f739b2a5f492c2`); CryptoMiniSat 5.18.0 (tag `release/v5.18.0`, commit
`97c6efeae45d93c45d2ebc3e4e83c2014c79513d`, built `-DNOCADICAL=ON`); GMP 6.3.0. Tarball sha256s are
pinned in `tools/external/provision-sat.sh`.

---

## 1. Scope, and what changed since the issue was written

- **"Blocked on G2" no longer holds.** G2 (#218) closed; its implementation (#233) gave a working
  characteristic-two pipeline and `grobner::field_equations` — see
  [`boolean-solving.md`](boolean-solving.md) §3 and §5. Everything below runs on that path, with
  `Zp2` and `with_field_equations`.
- **Public instances only.** #220 asked for G1's instances. Those, and G1's baselines, are not part of
  this public repository and are **out of scope for this record**: nothing here uses, cites or
  depends on them. Every instance is a random quadratic system over `GF(2)` with a planted solution,
  generated in `examples/sat_algebra.rs` from a fixed seed (#272's construction, as
  `examples/gf2_f4_dispatch.rs` builds it: each `x_i x_j`, `i <= j`, with probability 0.5; for §4,
  plus affine forms with each variable at probability 0.5). Anyone can regenerate them.
- **#220's `full-width-poseidon.md` §4.2 warning is not carried.** That document is no longer in this
  repository, so it is not cited; §4 measures the analogous question directly instead.
  `src/grobner/research/linear.rs` is now `src/grobner/transform/affine.rs`.
- **Nothing in `src/` changed.** The converter, the XOR export and the model lift are measurement
  scaffolding in `examples/sat_algebra.rs`, not a backend. No Cargo dependency was added.

## 2. Q1 — what is lost in ANF→CNF, measured

The Bard–Courtois–Jefferson route: each monomial of degree `d >= 2` gets one Tseitin AND variable
(`d + 1` clauses, shared across equations), and each equation becomes an XOR over those variables. An
uncut XOR of length `L` is `2^(L-1)` clauses — one per assignment of the wrong parity. Cutting at
length `c` chains chunks through fresh variables at `2^(c-1)` clauses per `c - 2` inputs absorbed.
`examples/sat_algebra.rs`' tests check the encoding against brute force (the CNF's solutions,
projected to the `x_i`, are exactly the ANF's) and its size against that closed form.

```sh
cargo run --release --example sat_algebra -- clauses
```

**The input systems** (clauses / variables at each cut length):

| instance | equations | ANF terms | longest XOR | uncut, for that XOR | cut 3 | cut 4 | cut 5 | cut 6 |
|---|---|---|---|---|---|---|---|---|
| MQ n=20 m=20 | 20 | 2094 | 115 | 2^114 | 8786 / 2244 | 8786 / 1223 | 11498 / 881 | 16878 / 712 |
| n=24: 18 quadratics + 6 affine | 24 | 2807 | 166 | 2^165 | 11864 / 3035 | 11864 / 1661 | 15512 / 1205 | 22780 / 975 |
| same, affine-eliminated (n=18) | 18 | 1496 | 98 | 2^97 | 6299 / 1613 | 6299 / 886 | 8227 / 645 | 12071 / 523 |

**The Macaulay rows** of a real `GF(2)` F4 run on MQ `n = m` with field equations — every matrix
`F4Options::default()` builds, read as one XOR per row with the constant column as right-hand side:

| instance | matrices | rows | nonzeros | longest row | uncut, for that row | cut-4 clauses | cut-4 clauses per nonzero |
|---|---|---|---|---|---|---|---|
| MQ n=8 | 5 | 588 | 4431 | 21 | 2^20 | 13731 | 3.1 |
| MQ n=10 | 5 | 1647 | 29949 | 42 | 2^41 | 108370 | 3.6 |
| MQ n=12 | 6 | 2964 | 88636 | 92 | 2^91 | 334827 | 3.8 |
| MQ n=14 | 6 | 9421 | 464645 | 155 | 2^154 | 1788279 | 3.8 |

What this says, which the issue's framing ("exponential in their length") only half-states:

1. **The exponential is real and irrelevant: nobody encodes uncut.** A dense quadratic in 20 Boolean
   variables already has a 115-term XOR, `2^114` clauses. A 155-term Macaulay row is `2^154`.
2. **Cut, the blow-up is a constant: about 4 clauses per XOR term.** Cut 3 and cut 4 cost the same
   clauses (`2^(c-1)/(c-2)` is 4 at both) and cut 4 halves the extra variables; above 4 the clause
   count grows. The Macaulay rows land at 3.1–3.8 clauses per nonzero. Size is not the problem.
3. **What is lost is the algebra, not the bytes.** A cut XOR is a chain of small parity constraints
   linked by fresh variables, and unit propagation over that chain cannot add two rows together.
   Every row operation F4's elimination does in one `xor` is, to a CDCL solver over the CNF, a
   derivation it has to discover by search. §3's "no Gauss" column is that loss measured: plain CDCL
   on the cut encoding of a consistent linear system, which Gaussian elimination solves outright,
   failed to decide three of the four largest matrices in 30 s.

So the issue's premise holds in the form that matters: **a Macaulay row is the worst case for CNF**,
not because the clause count explodes but because CNF is the representation in which the one thing
F4 does to a row is not an available inference.

## 3. Q6 — Zeebra's `GF(2)` elimination against CryptoMiniSat's Gaussian elimination

The step that #220 called "useful regardless of every other answer". The matrices are the ones a
real F4 run builds — replayed from `trace_batches` through symbolic preprocessing and
`MacaulayMatrix::build`, the way `examples/boolean_density.rs` and `f4_blocks.rs` do — on MQ `n = m`
for `n = 8, 10, 12, 14` with field equations, seed 220: 22 matrices from 19x44 to 5364x1937.

```sh
tools/external/provision-sat.sh                               # ZEEBRA_EXT_PREFIX off $HOME
cargo run --release --example sat_algebra -- replay 3
```

Per matrix, in this order:

1. `Dense`, `Sparse` and `Adaptive` (`linalg::row_echelon_with`) eliminate a clone each, interleaved
   in rotating order, minimum of 3; the three are **asserted to produce the same matrix and the same
   `EliminationStatistics`**. The bit-packed kernel (`linalg::gf2`, #272/#777) runs too, with the
   packing in its own column, and is asserted to agree on rank.
2. The matrix is exported as XOR constraints — each non-constant column a variable, the constant
   column the right-hand side — with the export in its own column.
3. **The independent check, before any CMS time is kept.** `tools/external/cms-xor-driver` loads the
   XORs into a fresh CryptoMiniSat and computes the solution space's dimension by using CMS only as a
   satisfiability oracle: fix variables one at a time to a model's value, and count those whose other
   value is still feasible. **Rank and dimension are asserted equal to Zeebra's** (`rank =
   variables - dimension`; Zeebra's dimension is the non-constant column count minus its rank). A
   disagreement would be a defect in one of them. **All 22 agreed.** A matrix CMS could not decide
   would get no agreement and no time; none needed that.
4. Only then: CMS's first `solve()` of the same XORs with Gauss–Jordan on (minimum of 3,
   `autodisablegauss` off so it cannot quietly drop the module), and once with it off.

Times in microseconds. `CMS GJ` is the number of Gauss–Jordan matrices CMS's own log reports
building; `?` means it logged none because propagation and equivalence substitution decided the
system before matrix initialization.

| matrix | rows x cols | rank | dim | row ops | Dense | Sparse | Adaptive | Adaptive ns/op | packed (pack + RREF) | CMS GJ | CMS Gauss | CMS no Gauss |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| n=8 #1 | 146x161 | 141 | 20 | 1053 | 93 | 245 | 71 | 67.0 | 2 + 64 | ? | 13510 | 13564 |
| n=10 #2 | 999x607 | 604 | 2 | 60338 | 5898 | 26442 | 4459 | 73.9 | 34 + 1555 | ? | 8909 | 9761 |
| n=12 #1 | 321x453 | 310 | 142 | 3007 | 674 | 2465 | 528 | 175.6 | 10 + 277 | 1 | 11426 | 100671 |
| n=12 #2 | 1815x1351 | 1348 | 2 | 174615 | 37450 | 189031 | 29297 | 167.8 | 121 + 6798 | 1 | 1963757 | 368973 |
| n=14 #1 | 430x677 | 417 | 259 | 4424 | 1567 | 5263 | 1074 | 242.8 | 17 + 485 | 1 | 12944 | undecided at 30 s |
| n=14 #2 | 2809x2393 | 2301 | 91 | 429445 | 183750 | 1048018 | 145891 | 339.7 | 272 + 20969 | 1 | 2429394 | undecided at 30 s |
| n=14 #3 | 5364x1937 | 1936 | 0 | 1027081 | 247069 | 856983 | 122428 | 119.2 | 368 + 29174 | 1 | 12411510 | undecided at 30 s |
| **all 22** | | | | 1736325 | 478981 | 2137365 | 306032 | 176 (aggregate) | 61389 | | 16902635 | 3 undecided |

The full 22-row table, with nonzeros, peak live entries, packed row-xor counts and export times, is
`research/sat-and-algebra/replay.md`.

**The result:** on the same matrices, with rank and dimension agreeing, **CryptoMiniSat's Gaussian
elimination took 55x Zeebra's `Adaptive` backend in aggregate and 275x the bit-packed kernel**; on
the three largest it was 17–100x `Adaptive`. Without Gauss, CDCL did not decide three of the seven
matrices above inside 30 s. On the small matrices CMS's floor is about 0.7 ms of solver start-up
against Zeebra's single-digit microseconds, which is not a fair comparison of elimination and is not
the one drawn.

**Why, which is the transferable part.** These are not the same operation, and the difference is the
point rather than a confound:

- CMS's Gauss–Jordan (Han–Jiang style, "Gauss-E in a Simplex way" in its banner) is a **propagation
  engine inside search**: it maintains a matrix under the current partial assignment and reports
  implied literals and conflicts, and it is rebuilt or updated as the trail moves. It never sets out
  to compute a rank. Deciding a consistent system with dimension 91 means CDCL branching through
  free variables with Gauss keeping the trail consistent.
- F4's elimination computes the echelon form **once**, which is the object #58 established F4 needs
  — not a solve ([`wiedemann-krylov.md`](wiedemann-krylov.md) §1; not reopened here). The rank and
  the solution space fall out of it for free.

So the question "does Zeebra's sparse `GF(2)` elimination beat a SAT solver's internal one?" has a
plain answer, **yes, by one to two orders of magnitude on F4-shaped matrices**, and the reason is
that the SAT solver's module solves a harder-to-state problem incrementally. That **bounds every
hybrid ambition in the same direction**: there is nothing for Zeebra to borrow from CMS's XOR engine
for F4, and if anything the transfer would run the other way — a SAT solver handed an F4-reduced
system is handed the elimination it does worst.

Two defects in the instrument, recorded because they would have produced a wrong result:

- `set_allow_otf_gauss()` together with `autodisablegauss` off left `n=14 #1` (430x677, consistent,
  rank 417) **undecided after 60 s**; CMS's defaults decide it in 13 ms with the same matrix built,
  and so does the CMS binary. The driver therefore leaves that call out (comment in
  `cms_xor.cpp`).
- Sparse's per-operation cost (33–2440 ns, 1231 aggregate) is 0.6–7x `Adaptive`'s (Sparse is ahead only on the 68-entry `n=12 #5`), in line with
  [`boolean-solving.md`](boolean-solving.md) §15.2; `Adaptive` is what `F4Options::default()` uses.

## 4. Q4 — algebraic preprocessing, then kissat

The cheapest hybrid: let Zeebra remove what it removes exactly, and hand kissat the residual.
Instance: `n` variables, `n - k` random quadratics and `k` random affine forms (a cipher-like linear
layer), planted. Arm A is kissat on the cut-4 CNF of the whole system. Arm B is
`transform::eliminate_affine` + `AffineElimination::project` to `n - k` variables, CNF of the
projection, kissat, and the model lifted back with `AffineElimination::lift`. **Every model from
either arm is checked against the original equations.** Arms interleave with alternating order;
minimum of 3 (one run at `n = 24`, where a single run reaches 24 s). The F4 columns are `solve_one`
on the same two systems with field equations, as option 1's comparison from Zeebra's side.

```sh
cargo run --release --example sat_algebra -- preprocess 3
```

Wall milliseconds; `ratio` is (eliminate + kissat) / kissat alone.

| instance | CNF clauses / vars | after elimination | kissat alone | eliminate + kissat | of which eliminate | ratio | F4 solve_one alone | F4 after elimination |
|---|---|---|---|---|---|---|---|---|
| n=16: 12 quadratics + 4 affine, seed 1 | 3636 / 533 | 2058 / 301 | 53.5 | 27.3 | 1.07 | 0.51 | 51.5 | 183.0 |
| n=16: 12 quadratics + 4 affine, seed 2 | 3564 / 525 | 1922 / 285 | 93.6 | 30.4 | 0.93 | 0.32 | 49.3 | 326.8 |
| n=16: 12 quadratics + 4 affine, seed 3 | 3596 / 529 | 1894 / 280 | 70.4 | 41.7 | 0.84 | 0.59 | 266.0 | 204.2 |
| n=16: 12 quadratics + 4 affine, seed 4 | 3612 / 530 | 2046 / 300 | 30.7 | 25.5 | 0.70 | 0.83 | 45.8 | 38.5 |
| n=16: 12 quadratics + 4 affine, seed 5 | 3612 / 531 | 1974 / 290 | 26.8 | 38.6 | 0.81 | 1.44 | 249.0 | 242.4 |
| n=20: 15 quadratics + 5 affine, seed 1 | 7050 / 1007 | 3775 / 542 | 561.9 | 47.2 | 2.31 | 0.08 | 35478.0 | refused: `TooManyColumns` (200 000) |
| n=20: 15 quadratics + 5 affine, seed 2 | 6946 / 993 | 3851 / 553 | 130.5 | 67.9 | 2.03 | 0.52 | 2653.2 | 2064.2 |
| n=20: 15 quadratics + 5 affine, seed 3 | 6882 / 983 | 3859 / 553 | 41.3 | 87.3 | 2.33 | 2.11 | 20416.4 | 2088.6 |
| n=20: 15 quadratics + 5 affine, seed 4 | 6974 / 994 | 3711 / 532 | 687.2 | 318.8 | 2.19 | 0.46 | 15887.7 | 14615.4 |
| n=20: 15 quadratics + 5 affine, seed 5 | 6774 / 970 | 3699 / 532 | 558.8 | 24.5 | 2.16 | 0.04 | 2737.5 | 1919.0 |
| n=24: 18 quadratics + 6 affine, seed 1 | 11864 / 1661 | 6299 / 886 | 23555.1 | 585.6 | 4.42 | 0.02 | not run | not run |
| n=24: 18 quadratics + 6 affine, seed 2 | 11816 / 1658 | 6575 / 922 | 13713.7 | 1846.3 | 4.12 | 0.13 | not run | not run |
| n=24: 18 quadratics + 6 affine, seed 3 | 11600 / 1629 | 6383 / 898 | 967.5 | 409.3 | 5.15 | 0.42 | not run | not run |
| n=24: 18 quadratics + 6 affine, seed 4 | 11628 / 1631 | 6455 / 908 | 10315.6 | 2759.1 | 4.72 | 0.27 | not run | not run |
| n=24: 18 quadratics + 6 affine, seed 5 | 11432 / 1606 | 6387 / 899 | 11687.3 | 3200.7 | 4.77 | 0.27 | not run | not run |

**Reading it:**

1. **Affine elimination before kissat won on 13 of 15 instances**, with geometric-mean ratios of
   0.65 at `n = 16`, 0.28 at `n = 20` and 0.15 at `n = 24` (0.30 over all 15). The gain grows with
   size, and the elimination itself is 1–5 ms against kissat's tens of milliseconds to tens of
   seconds. It removes a quarter of the variables and about 45% of the clauses — the affine forms
   are the longest XORs in the system (half the variables each), which is exactly what §2 says CNF
   handles worst.
2. **It is not uniform.** Two instances got slower (1.44x, 2.11x), and per-instance CDCL variance
   swamps repetition noise (kissat alone ranges 41–687 ms across five `n = 20` seeds). Five seeds
   per size is enough for the direction, not for a constant.
3. **The direction is the reverse for F4, which is the warning worth carrying.** The same projection
   made `solve_one` **slower** on 2 of 5 `n = 16` instances (3.6x and 6.6x), roughly neutral on the
   rest, and on `n = 20` seed 1 turned a 35 s solve into a refusal at the default 200 000-column
   budget. Substituting affine expressions into quadratics densifies them, and F4 already absorbs a
   linear equation for almost nothing; CDCL does not. **Cheaper for one engine is not cheaper for
   the other**, so a preprocessing step cannot be judged by the size of what it emits.
4. **Option 1's comparison, from Zeebra's side:** on these random dense Boolean systems kissat beat
   F4's `solve_one` by 5–494x at `n = 20` (both on the unprojected system). That is a statement
   about random Boolean MQ at this size, where SAT is known to be strong, and not about structured
   instances; it is the reason option 1 is worth having as a baseline at all.

**Decision: preprocessing is deferred, not adopted.** It works, and it is cheap, but the thing being
sped up is kissat, which is not part of Zeebra; building "Zeebra preprocesses, then SAT" into the
crate would be option 2 by another door. What Zeebra provides is already public —
`transform::eliminate_affine`, `project`, `lift` — and any SAT pipeline can call it. **Trigger to
reopen:** a structured public instance family where (a) Boolean instances matter to the crate per
#196, and (b) affine elimination *plus a nonlinear step Zeebra owns* (a partial F4 degree, ElimLin
iterated) beats kissat alone by more than this table's median. On random quadratics, linearizing the
quadratic part exposes no new affine equations until `m` approaches the number of quadratic
monomials, so an ElimLin iteration beyond the first affine pass has nothing to find here; that is
why it is not in the table.

## 5. Q3 — does CDCL's learning offer anything to F4's pair selection? No

Analytic, as #220 asked; the expected negative, with the reasoning written out. #58's position that
F4's echelonization is not a black-box solve is used here by analogy and not reopened.

1. **CDCL learns because it searches; F4 does not search.** A learned clause is the negation of a
   conflicting partial assignment, cut from the implication graph, and its value is that it prunes
   *other branches*. F4 has no branches: pair selection orders a saturation that reaches the same
   reduced Gröbner basis under every schedule ([`pair-scheduling.md`](pair-scheduling.md) §1 — "no
   schedule can change the answer"). There is nothing to backjump to, and no part of the space a
   learned fact would cut off.
2. **A zero reduction carries no explanation in the CDCL sense.** A conflict is attributed to the
   decisions that caused it. A pair row that reduces to zero is a *syzygy* — a linear combination of
   the rows above it — and F4's elimination does not record which combination; the transformation
   matrix is discarded. There is no "reason" to analyse.
3. **The explanation it would need is exactly a signature.** Tracking, per row, the leading term of
   the module element it came from is the signature apparatus; and the "learned clause" that avoids
   future zero reductions is F5's syzygy and rewrite criteria. So the CDCL analogue for F4 **already
   exists, under its own name**, and Zeebra measured its ceiling: 33–60% of pair rows add no rank
   ([`signature-based.md`](signature-based.md)), and signature F4 is now M30/M31's work
   (`src/grobner/sigf4/`, [`m31-baseline.md`](m31-baseline.md)). A CDCL-flavoured version would be a
   worse rediscovery of that.
4. **What the counters already say.** `examples/f4_statistics.rs` counts Buchberger's zero
   reductions and `examples/pair_criteria.rs` what each criterion discards. Both are criteria —
   theorems that a pair is useless — rather than heuristics learned from a run; a learned heuristic
   that discarded a pair a theorem does not cover would be unsound, because a pair that reduced to
   zero once is not zero after the basis changes.

**Won't do.** Reopen only with a concrete construction that extracts a reusable, sound fact from a
zero reduction that is not a signature criterion.

## 6. Q5 — branch-and-solve, guessing and field equations: deferred to #75

Guessing `k` Boolean variables and solving the `2^k` specialized systems — with SAT or with F4 — is
crossbred's elimination/enumeration trade-off under another name, and #75 (B2) owns it with the
accounting rule that matters: **the cost is the sum over all `2^k` guesses, not the size of one
reduced system**. Over `GF(2)` the enumeration is a Möbius transform over the Boolean hypercube,
which #75 already notes. #75 has since closed with a no-go for Zeebra; this record does not duplicate
that analysis and does not reopen it. The only thing #220 adds is the observation that a SAT solver's
own branching is the same trade-off made implicitly and adaptively — which is why "SAT plus field
equations" is not a separate question from #75's.

## 7. Q2 — the backend decision, and the policy question kept separate

**Policy, answered on its own:** an external SAT dependency is **not acceptable as a component**,
and acceptable as an oracle. This is not a judgement about SAT; it is the rule the crate already
lives by.

- The README's promise is "plain Rust, generic over a `FiniteField` trait, stable toolchain, **no C
  dependencies and no linked algebra system**", and the crate ships nothing third-party at run time.
- [`external-provenance-policy.md`](external-provenance-policy.md) §2.1: linking an LGPL or other C
  library "should be read as 'not available here' unless a separate decision is taken to introduce C
  linkage", with the relinking, build-system and `cargo build`-is-the-whole-build costs that brings.
  kissat (MIT) and CryptoMiniSat (MIT, with a `-DMIT=ON` build option that excludes its components
  under other licences) are C/C++ libraries, so linking either would be exactly that decision.
- The precedent for external tools is **oracles, not components**: Singular, msolve, Groebner.jl,
  Sagebrush and FLINT are run as separate processes in tests and benchmarks and never linked. kissat
  and CMS now sit in the same place (`tools/external/provision-sat.sh`).
- A vendored CDCL implementation sits worse: it would be a second solver to maintain, outside the
  crate's subject, with none of the published-reference and Sage-interoperability properties the
  README asks of an algorithm here.

**Technical merit, answered separately:** even with the policy waived, a backend is not worth having.

- §2: the converter is easy and the CNF is small (about 4 clauses per term), but it is the
  representation in which F4's one operation, adding rows, is not an inference.
- §3: the XOR-aware engine SAT uses to recover that is 55x slower than Zeebra's elimination on F4's
  own matrices. A Zeebra front-end would hand Boolean instances to the slower linear algebra.
- §4: where SAT wins outright on an instance, the user wants kissat, and should run kissat; a
  `solve_one`-shaped wrapper adds a model lift and a subprocess protocol and nothing else. That is
  what option 1 already provides as a measurement, without making Zeebra a SAT front-end on Boolean
  instances — a change of identity for a crate whose subject is computational algebra.
- No public-API gap was found that would need `src/grobner/f4/`, `src/grobner/sigf4/` or
  `src/linalg/` to change; nothing is filed.

**Decision: option 2 won't do.** No dispatch policy is deposited in `src/grobner/planning/` (#95's
M21-D would have been its home). Reopen only if the policy in §7 changes first — that is, if the
crate decides to take run-time C dependencies for some other reason — and then with a measurement on
the instances at issue showing SAT beating F4 by more than the conversion and lift cost.

## 8. Reproducing

```sh
export ZEEBRA_EXT_PREFIX=/buildcache/<you>/sat-prefix      # not under $HOME, not on tmpfs
tools/external/provision-sat.sh                            # GMP, kissat, CMS, cms-xor-driver
cargo test --example sat_algebra                           # encoding, export and lift, checked
cargo run --release --example sat_algebra -- clauses       # §2
cargo run --release --example sat_algebra -- replay 3      # §3, asserts before it times
cargo run --release --example sat_algebra -- preprocess 3  # §4, every model checked
```

Without the solvers in the prefix, `replay` and `preprocess` print `not run` / nothing measured rather
than failing. `ZEEBRA_SAT_SKIP_F4=1` skips `preprocess`' F4 columns.

## 9. References

- Soos, Nohl, Castelluccia, *Extending SAT Solvers to Cryptographic Problems*, SAT 2009 —
  CryptoMiniSat's XOR clauses and Gaussian elimination inside CDCL (§3).
- Bard, Courtois, Jefferson, *Efficient Methods for Conversion and Solution of Sparse Systems of
  Low-Degree Multivariate Polynomials over GF(2) via SAT-Solvers* — the conversion and cutting
  number of §2.
- Courtois, Bard, *Algebraic Cryptanalysis of the Data Encryption Standard* — ElimLin, the
  preprocessing hybrid of §4.
- Brickenstein, Dreyer, *PolyBoRi*, J. Symbolic Computation 44 (2009) — the Boolean representation.
- Faugère, *A new efficient algorithm for computing Gröbner bases without reduction to zero (F5)*,
  ISSAC 2002 — the signature criterion of §5.
- kissat, <https://github.com/arminbiere/kissat>; CryptoMiniSat, <https://github.com/msoos/cryptominisat>.
- #58 / [`wiedemann-krylov.md`](wiedemann-krylov.md) §1 — F4's echelonization is not a black-box
  solve; cited, not relitigated.
