# Why the signature engine is 400× slower than F4 on `sd-hairer-2` (#1136)

**Measured at:** branch `research/1136-hairer2-attribution` from `main` `a63c5568`. Apple M-series
laptop (macOS), release build, 1 worker, unpinned. **Status:** attribution complete, 2026-11-25.
**Parent:** #1003. **Found by:** #1015.

The deciding quantities are deterministic operation counts: coefficient products, elements, batches
and signature degrees. These do not depend on the machine. Wall times are given for scale only and
are not a Threadripper measurement. Fitted-row cells are medians of 5 solves in one process. T1
cells (§6) are one solve each. Data, scripts and tables:
[`research/1136-hairer2-attribution/`](../../research/1136-hairer2-attribution/README.md).

## 1. Result

The slowdown has two multiplicative parts. Neither is caused by the linear generators.

1. **Signature degree rather than polynomial degree (28×).** The engine forms batches by Schreyer
   signature degree. Under grevlex that is the sugar degree, `deg t + deg lm(f_i)`. A row whose
   leading terms cancel, so that its degree falls, stays at the degree of its signature. So the
   engine does not benefit from degree falls, and on `sd-hairer-2` it does the same work as on the
   input homogenized by one extra smallest variable `h`: coefficient products agree to 0.02%,
   elements added 2,680 against 2,681, and both stop at signature degree 18. Conventional F4 does
   use the degree falls. On the affine input its largest pair degree is 7. On the homogenized
   input it needs degree 16 and takes 28× as long.
2. **Signature basis far larger than the Gröbner basis (13×).** On the *same* homogenized input
   the engine is still 13× slower than F4. It adds 2,681 elements against F4's 502, and 2,175 of
   them already have a lead divisible by an existing lead when they are added. Building their
   reducer rows (2.28 M) is the symbolic stage, at 53% of the run.

The cause is labelled **distribution-specific**. The predeclared test of part 1 on 47 development
rows (§6) held on 43 and failed on 4, so "same work as the homogenization" is not a general rule.
On every row read, though, the affine run did no more than 1.0002× the homogenized run's work.

## 2. Reproduction

| | conventional F4 | signature engine | ratio |
|---|---:|---:|---:|
| #1012 record (Threadripper, P1 / P4) | 49 ms | 17,462 ms | 357 (400 against the cheapest arm) |
| this Mac, median of 5 | 23.8 ms | 11,046 ms | 464 |

Both return the same reduced basis (72 elements, equal `reduced-basis` digest).

## 3. Hypotheses refuted on the fitted rows

Derived presentations are written by
[`derive.py`](../../research/1136-hairer2-attribution/derive.py). Each generates the same ideal, or
(substituted) the ideal after the linear generators eliminate four variables.

| `sd-hairer-2` presentation | F4 ms | signature ms | ratio | signature products | elements added |
|---|---:|---:|---:|---:|---:|
| panel record | 23.8 | 11,046 | 464 | 637.3 M | 2,680 |
| generators reversed (= by descending degree) | 22.9 | 11,461 | 500 | 637.8 M | 2,687 |
| 4 linear generators substituted out (7 generators, 9 variables) | 18.1 | 10,005 | 552 | 660.3 M | 2,742 |
| substituted, then reversed | 18.3 | 10,078 | 552 | 672.7 M | 2,814 |

- **The linear generators are not the cause.** Substituting them out leaves the signature engine's
  work at +3.6% and the ratio at 552×.
- **Generator order is not the cause.** Reversing the order changes the products by +0.07% here,
  +1.9% after substitution, and −4.3% on `sd-butcher`.

## 4. Decomposition

`sig(affine) ÷ F4(affine) = [F4(homog) ÷ F4(affine)] × [sig(homog) ÷ F4(homog)] × [sig(affine) ÷ sig(homog)]`

| source | sig ÷ F4 | degree falls: F4 homog ÷ F4 affine | basis size: sig homog ÷ F4 homog | sig affine ÷ sig homog | sig products, affine ÷ homog |
|---|---:|---:|---:|---:|---:|
| `sd-hairer-2` | 464 | 28.0 | 13.3 | 1.25 | 1.0002 |
| `sd-hairer-2`, substituted | 552 | 29.7 | 15.2 | 1.23 | 0.9997 |
| `sd-butcher` | 81 | 8.5 | 10.4 | 0.91 | 1.0000 |
| `sd-butcher`, substituted | 58 | 8.2 | 7.6 | 0.93 | 1.0000 |

`sd-butcher` (12× in #1012, 81× here) has the same structure with smaller factors.

The last factor is a cost per product, not extra work. The affine run makes the same products but
takes 1.25× as long on `sd-hairer-2`: symbolic preprocessing takes 6.5 s against 4.7 s, and it
builds 4.28 M reducer rows against 2.28 M. This was not attributed further.

## 5. Where the 11 s goes on `sd-hairer-2`

| stage | ms | share |
|---|---:|---:|
| symbolic preprocessing | 6,457 | 58% |
| elimination | 2,519 | 23% |
| bookkeeping (pairs, criteria, queue) | 346 | 3% |

The engine makes 3,019 targets and 4.28 M reducer rows, about 1,400 reducer rows per target. It
creates 3.59 M pairs. The criteria remove them as follows: 2.04 M Koszul, 1.13 M zero-row syzygy,
278 k product criterion, 103 k rewrite and 34 k duplicate. 339 targets reduce to zero.

By signature degree (full table in
[`tables.md`](../../research/1136-hairer2-attribution/tables.md)), the last element of the minimal
basis is added at signature degree 14. Degrees 15–18 add 245 elements, none of them in the minimal
basis, and take 6.3 s, which is 57% of the run. Conventional F4's batch degrees never exceed 7. Most
of the cost is spent proving completeness at signature degrees F4 never reaches. That is the
question #1140 opens for graded-lex: an early-termination certificate. This record suggests it
matters under grevlex too.

## 6. Out-of-sample test T1 (predeclared, falsified)

Predeclared in the
[README](../../research/1136-hairer2-attribution/README.md#predeclared-out-of-sample-test-written-before-the-development-read-below)
before the read. For every M34 development record at `p31` that is non-homogeneous, has at most
13 variables and is outside the fitted family (47 records), the signature engine's coefficient
products on the record and on its homogenization agree within [0.99, 1.01].

**Result: 43 in the band, 4 outside it, 0 undecided.** The claim does not hold as a general rule.

| record | products, affine ÷ homogenized |
|---|---:|
| `gen-phosphorylation-2-nonzero@p31` | 0.452 |
| `gen-phosphorylation-2@p31` | 0.511 |
| `gen-phosphorylation-3@p31` | 0.460 |
| `zb-col-gnm-12-17-s2@p31` | 0.986 |

All four failures are on the side where the affine run is *cheaper*. These are small problems, under
7,400 products. In the affine ring a reducer whose degree fell divides more leads than its
homogenization does, because the homogenized reducer carries a power of `h`. That is a plausible
mechanism, but it was not tested. Across all 51 rows read (47 development and 4 fitted
presentations), the affine run never did more than 1.0002× the homogenized run's products.

The weaker statement is therefore labelled **hypothesis**: the signature engine's work on an affine
grevlex input is at most its work on the homogenization, and usually equal to it. It has been read
on development rows only.

T1 also shows that the degree-fall factor (F4 homog ÷ F4 affine) does not explain every large ratio
on its own:

| record | sig ÷ F4 | F4 homog ÷ F4 affine | F4 max pair degree, affine / homog |
|---|---:|---:|---|
| `zb-reimer-6@p31` | 25.9 | 14.1 | 12 / 22 |
| `zb-cyclic-7@p31` | 13.6 | 0.8 | 13 / 20 |
| `zb-col-ktree2-12-s1@p31` | 11.2 | 1.4 | 5 / 7 |
| `zb-katsura-12@p31` | 0.1 | 1.0 | 13 / 13 |

`reimer-6` matches the `sd-hairer-2` pattern. `cyclic-7` has no degree-fall factor, so its slowdown
is the basis-size part alone.

## 7. What this does and does not change

- **No default changes.** `GradedEngine::Adaptive` already routes both records to conventional F4
  (#1015). Only the forced engine is affected.
- **Not a selector feature.** The degree-fall factor costs a second F4 run to observe. No cheap
  input feature for it was tested, and any rule fitted on these rows would need rows it was not
  fitted to (#1136 constraint).
- **Engine direction, for whoever takes it up.** Two parts are open: (a) completeness work above
  the last minimal-basis element (§5, with #1140), and (b) the dominated-at-birth elements on
  homogeneous input. Neither is attempted here.

## 8. Reproduce

See [`research/1136-hairer2-attribution/README.md`](../../research/1136-hairer2-attribution/README.md).
The harness is `examples/sig_f4_study.rs`, whose new `--catalog` flag reads a `corpus-instance-v1`
record, built with `--features research-sigf4-usage`.
