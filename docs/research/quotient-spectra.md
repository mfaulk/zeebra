# Bounded quotient spectra

Implementation and feasibility check for #686. Mathematical implementation is
independent of external source code. The public contract, budget accounting and
Berkowitz recurrence are in the
[quotient operator guide](../guide/grobner-bases.md#quotient-operator-polynomials).

Exact tests cover nonradical and nonseparating examples, characteristic two and
three, GF(32003), GF(256), BN254, zero multiplication, unit and zero ideals,
cyclic nilpotents and a field quotient. A separate permutation expansion of
`det(tI-T)` verifies every characteristic coefficient on dimension-four examples;
full-operator annihilation and minimal-divides-characteristic are also checked.
The shared first Krylov dependence establishes minimality and agrees with the
existing shape diagnostic. Typed refusal tests include exact work/workspace
boundaries, invalid variables, dimension limits and zero duration.

The initial implementation uses conservative defaults D<=128, 30 seconds,
256 MiB incremental workspace and 100 million coefficient-update work units.
A bounded eight-fixture run at D={4,16,64,128}, with sparse and dense operators,
will check their affordability. No speedup or solver strategy change is claimed.
