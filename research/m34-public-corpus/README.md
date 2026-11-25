# #1006: public application panel

This is M34's public application corpus ([plan §8.2](../../docs/MILESTONE-GENERALIZABLE-SELECTION.md)).
It holds **62 base problems in 23 families**. 43 are exact integer systems from the SymbolicData
collection. 19 come from two application models outside it, built by independently written
generators: the Chandrasekhar H-equation and n-site phosphorylation steady states. Each problem is
admitted at two fields, 2³¹−1 (`p31`) and 2⁶⁴−59 (`p64`), with grevlex and task `T-GB`. That gives
124 `corpus-instance-v1` records under the [lineage contract](../../docs/research/corpus-lineage.md).

This slice is **not a cohort freeze**. The panel is admitted but unsplit; #1005's separate freeze
commit draws the cohorts once #1006 and #1007 are complete. No solver timings are recorded here,
and the Singular reference runs are not measurements.

| File | Role |
|---|---|
| `panel.json` | Hand-curated selection: problem id, upstream entry or generator call, `family_id`, `source_id`, `formulation_id`, parameters and presentation parents |
| `inputs.json` | Exact upstream SymbolicData equations, frozen by `import`, with each upstream file's SHA-256 |
| `catalog.json` | Generated records, one per line. CI rebuilds them from `inputs.json` and the generators in `tools/m34_public_corpus.py`, and compares the bytes |
| `references.json` | Reduced-basis digests for every record: Singular at `p31`, certified grobx at `p64`. The basis text itself is not stored |
| `composition.json` | Per-family counts, scales and frontier rows for the §8.2 composition read, written by `catalog` and checked by `check` |

## Reproduce

```sh
python3 tools/test/m34-public-corpus-test.py
python3 tools/m34_public_corpus.py check
python3 tools/corpus_lineage.py validate research/m34-public-corpus/catalog.json
# Re-import (needs the pinned upstream checkout, not needed in CI):
gh api repos/symbolicdata/data/tarball/a5cdf5366150bffba22a2c91a86a012dd23831af > sd.tgz
tar xzf sd.tgz && python3 tools/m34_public_corpus.py import symbolicdata-data-a5cdf53
python3 tools/m34_public_corpus.py catalog
# References: Singular (build 44105) at p31, certified grobx 0.155.1 at p64
# (tools/external/grobx-driver); about 10 minutes at --jobs 12, untimed:
python3 tools/m34_public_corpus.py references --timeout 120 --grobx-timeout 300 --jobs 12
# Only rows that are missing or whose input digest changed (new or changed rows only):
python3 tools/m34_public_corpus.py references --missing --timeout 120 --grobx-timeout 300 --jobs 12
```

Run these from the repository root with Python 3.9 or newer, standard library only. Extract the
tarball outside the repository.

## Sources and licensing

| Source | Licence, as verified | Decision |
|---|---|---|
| [SymbolicData](https://github.com/symbolicdata/data) `a5cdf536`, `XMLResources/IntPS` | **CC0-1.0**. Asserted for the Data Catalogue at `RDFData/SymbolicData.ttl:13` and `RDFData/Systems.ttl:12`. The repository has no root licence file | **Admitted.** Exact integer equations are imported verbatim; the per-file SHA-256 is in `inputs.json` |
| Chandrasekhar H-equation: S. Chandrasekhar, *Radiative Transfer* (1950); collocation as in C. T. Kelley, [J. Math. Phys. 21 (1980) 1625](https://doi.org/10.1063/1.524647) | Model from the literature. Generator `chandrasekhar_h` written for Zeebra, MIT | **Admitted.** No third-party code. Groebner.jl's `chandra` was the discovery pointer and was not read |
| n-site phosphorylation: L. Wang and E. D. Sontag, [J. Math. Biol. 57 (2008) 29–52](https://doi.org/10.1007/s00285-007-0145-z) | Reaction network from the paper. Generator `multisite_phosphorylation` written for Zeebra, MIT | **Admitted.** No third-party code or model file |
| Groebner.jl benchmark generators (Demin & Gowda, [arXiv:2304.06935](https://arxiv.org/abs/2304.06935), pinned `54c9d643`) | GPL-2.0 ([provenance policy](../../docs/research/external-provenance-policy.md) table) | **Discovery only.** Generator code is not copied. Chandra is admitted from its primary source, above. Henrion, Hexapod and IPP are excluded below |
| [StructuralIdentifiability.jl](https://github.com/SciML/StructuralIdentifiability.jl) and SIAN exports | MIT (GitHub classifier; root file not read) | **Excluded for M34.** The exported system is what would be admitted, and neither package is installed here (`~/.julia` has Groebner.jl only). SIAN's export also substitutes random values, so each export would be a new seeded formulation |
| Macaulay2 `ExampleSystems` | GPL-2.0-or-later (provenance policy table) | **Discovery and cross-check only.** Its models overlap SymbolicData; overlapping models are linked through `source_id`, not double-counted |
| [MathRepo](https://mathrepo.mis.mpg.de/) ligand-binding systems | **No licence stated.** The site shows only "© Copyright 2026, Max Planck Institute for Mathematics in the Sciences" and a Terms of Use link (read 2026-11-25) | **Excluded:** unclear licence, per #1006's stop condition |
| PHCpack demo database | Not reviewed for admission | **Discovery only**, per #1006: its entries are often floating-point |

The CC0 statement covers the catalogue as a whole. The `IntPS` XML files carry no per-file licence,
so the catalogue-level dedication is the grant relied on. The upstream entries record their
contributors and creation dates (`createdBy`, `createdAt`); the original publications are listed in
SymbolicData's `RDFData/Bibliography.ttl`.

## Panel

`n` and `m` are the number of variables and generators. *Dimension* is from Singular at `p31`.
"Frontier" means Singular's `std` did not finish in 120 s; per #1006 such an input is retained with
`reference: none`. At `p64`, `sd-hairer-2` is also a frontier input: certified grobx did not finish
in 300 s. Its `p31` twin has a reference.

| Problem | Upstream entry | `family_id` | n | m | Dimension at p31 |
|---|---|---|---:|---:|---|
| `sd-signaltheory-f633` | `SignalTheory.f633` | `sd/signal-theory` | 10 | 9 | 2 |
| `sd-signaltheory-f744` | `SignalTheory.f744` | `sd/signal-theory` | 12 | 12 | 1 |
| `sd-signaltheory-f855` | `SignalTheory.f855` | `sd/signal-theory` | 14 | 15 | 1 |
| `sd-signaltheory-f966` | `SignalTheory.f966` | `sd/signal-theory` | 16 | 24 | frontier |
| `sd-verschelde-gametwo5` | `Verschelde.gametwo5` | `sd/gametwo-nash` | 5 | 5 | 0, vdim 44 |
| `sd-verschelde-gametwo6` | `Verschelde.gametwo6` | `sd/gametwo-nash` | 6 | 6 | 0, vdim 265 |
| `sd-verschelde-gametwo7` | `Verschelde.gametwo7` | `sd/gametwo-nash` | 7 | 7 | frontier |
| `sd-singular-schwarz-7` … `-11` | `Singular.schwarz_7` … `_11` | `sd/schwarz` | 7–11 | 7–11 | 0, vdim 2ⁿ |
| `sd-robot-fabrice24` | `Robot-Fabrice24` | `sd/robot-kinematics` | 9 | 9 | 0, vdim 40 |
| `sd-robot-romin` | `Robot-Romin` | `sd/robot-kinematics` | 12 | 7 | 5 |
| `sd-robot-rr` | `Robot-RR` | `sd/robot-kinematics` | 15 | 16 | 4 |
| `sd-robot-jcf26` | `Robot-jcf26` | `sd/robot-kinematics` | 34 | 34 | 0, vdim 40 |
| `sd-butcher` | `Butcher` | `sd/runge-kutta-order-conditions` | 8 | 8 | 3 |
| `sd-hairer-1` | `Hairer_1` | `sd/runge-kutta-order-conditions` | 8 | 6 | 2 |
| `sd-hairer-2` | `Hairer_2` | `sd/runge-kutta-order-conditions` | 13 | 11 | 2 |
| `sd-hairer-2-1` | `Hairer_2_1` (parent `sd-hairer-2`) | `sd/runge-kutta-order-conditions` | 13 | 12 | 2 |
| `sd-ellipsoid-2`, `-4`, `-m2` | `Ellipsoid_2`, `_4`, `_-2` | `sd/ellipsoid` | 10 | 4 | 6 |
| `sd-verschelde-virasoro` | `Verschelde.virasoro` | `sd/virasoro` | 8 | 8 | 0, vdim 256 |
| `sd-fourbodyproblem` | `FourBodyProblem` | `sd/four-body` | 6 | 6 | 0, vdim 84 |
| `sd-verschelde-chemkin` | `Verschelde.chemkin` | `sd/chemkin` | 13 | 13 | 0, vdim 40 |
| `sd-caprasse` | `Caprasse` | `sd/classical/caprasse` | 4 | 4 | 0, vdim 56 |
| `sd-cassou` | `Cassou` | `sd/classical/cassou` | 4 | 4 | 0, vdim 16 |
| `sd-trinks`, `sd-trinks-1` | `Trinks`, `Trinks_1` (parent `sd-trinks`) | `sd/classical/trinks` | 6 | 6, 7 | 0, vdim 10 and 2 |
| `sd-fee-2` | `Fee_2` | `sd/classical/fee_1` | 5 | 4 | 1; p64 frontier |
| `sd-fee-1` | `Fee_1` = `Fee_2(b=2)` (parent `sd-fee-2`) | `sd/classical/fee_1` | 4 | 4 | 0, vdim 26 |
| `sd-rose` | `Rose` | `sd/classical/rose` | 3 | 3 | 0, vdim 136 |
| `sd-schiele` | `Schiele` | `sd/classical/schiele` | 5 | 4 | 1 |
| `sd-schiele-1`, `sd-schiele-1-1` | `Schiele_1` (half-tangent substitution, parent `sd-schiele`), `Schiele_1_1` = `Schiele_1(p=1)` (parent `sd-schiele-1`) | `sd/classical/schiele` | 3, 2 | 2, 2 | 1; 0, vdim 38 |
| `sd-czapor-86a` | `Czapor-86a` | `sd/classical/czapor-86a` | 3 | 3 | 0, vdim 8 |
| `sd-weispfenning-94` | `Weispfenning-94` | `sd/classical/weispfenning-94` | 3 | 3 | 0, vdim 54 |
| `sd-raksanyi` | `Raksanyi` | `sd/classical/raksanyi` | 8 | 4 | 4 |
| `sd-bjoerk-8` | `Bjoerk_8` | `sd/classical/bjoerk_8` | 8 | 9 | unit ideal (basis {1}) |
| `sd-heron` | `Heron` | `sd/classical/heron` | 7 | 4 | 3 |
| `sd-geometry-heron-1` | `Geometry.Heron_1`: the same Heron area derivation in other coordinates, same contributor | `sd/classical/heron` | 6 | 3 | 3 |
| `sd-fourcircles` | `FourCircles` | `sd/classical/fourcircles` | 2 | 3 | 0, vdim 14 |

**Cross-check.** For every zero-dimensional problem where SymbolicData publishes a degree
(`sd:hasDegree`), Singular's `vdim` at `p31` agrees with it: Caprasse 56, Trinks 10, Trinks_1 2,
Fee_1 26, Rose 136, Czapor-86a 8, Weispfenning-94 54, FourCircles 14 and Schiele_1_1 38. That is evidence that the
import and the reduction modulo `p31` did not alter these ideals.

**Lineage choices.**
- `formulation_id` is the upstream entry, so a field twin is the same formulation (§8.2).
- `presentation_parent` links an `_1` variant or an upstream specialization (`Fee_1 = Fee_2(b=2)`,
  `Schiele_1_1 = Schiele_1(p=1)`) to its base where both are admitted.
- `support_id` is the computed `support-v1` digest; reduction removed no term at either prime.
- Each robot model has its own `source_id` but shares the family, so S2 keeps the family whole.
- The `sd/classical/*` problems are separate models from different authors, so each is its own
  family and source. Fee, Schiele and Heron have upstream entries at a second size and now cover
  two or three scales. The other nine cover one scale (see *Composition hand-off*).
- The `sd/schwarz` family comes from Singular's example collection. No application model is
  claimed for it.

## Generated application families

Both generators live in `tools/m34_public_corpus.py` and are rebuilt by `check` in CI. The record's
`source` names the paper, and its `transformations` list the parameter specialization before the
prime reduction.

| Problem | `family_id` | n | m | Dimension at p31 |
|---|---|---:|---:|---|
| `gen-chandrasekhar-h-4` … `-13` | `app/chandrasekhar-h` | 4–13 | 4–13 | 0, vdim 2ⁿ (16 … 2048) for n ≤ 11; n = 12, 13 frontier at both fields |
| `gen-phosphorylation-2` … `-7` | `app/multisite-phosphorylation` | 9–24 | 9–24 | 0, vdim 2·sites+1 (5 … 15) |
| `gen-phosphorylation-{2,4,6}-nonzero` (parent: the same `sites` without `-nonzero`) | `app/multisite-phosphorylation` | 10, 16, 22 | 10, 16, 22 | 0, vdim equal to the parent |

- **Chandrasekhar H-equation.** H(μ) = 1 + (c/2)·μ·H(μ)·∫₀¹ H(ν)/(μ+ν) dν, collocated at
  μᵢ = i/n with the n-point right-endpoint rule: 2n·Hᵢ − c·Hᵢ·Σⱼ i/(i+j)·Hⱼ − 2n = 0 for
  i = 1..n, with albedo c = 51/50. Each equation is scaled by the lcm of its denominators, which is
  exact over ℚ. Reduction refuses a prime dividing any of those denominators. They are primes
  ≤ 2n. 17 never appears, because it cancels against c = 51/50. At n = 13 they are 2, 3, 5, 7, 11, 13, 19 and 23, and each record's
  `clear-denominators` transformation lists them. Where a reference exists (n ≤ 11), the Bézout
  bound 2ⁿ is attained at both primes. n = 12 and 13 exceed both oracles' limits and are kept as
  frontier inputs.
- **Phosphorylation.** The sequential distributive network Sᵢ + E ⇌ ESᵢ → Sᵢ₊₁ + E and
  Sᵢ₊₁ + F ⇌ FSᵢ₊₁ → Sᵢ + F for i = 0..sites−1, under mass action. The equations are the ODE
  right-hand sides of every complex and of S₀..S_{sites−1}. The dependent rows (S_sites, E, F) are
  replaced by the three conservation laws. The rates at site i are (i+2, 1, i+1) for the kinase and
  (i+1, 2, i+3) for the phosphatase, with totals E = 7, F = 11 and S = 10·sites + 3. The specialization
  is a choice made here, recorded on every record. It is not taken from the paper. `n` in
  `family_parameters` is the variable count, so S3 scales on the same axis as the other families.
  `sites` is kept beside it.

**Inequations and saturation.** #1006 asks for tasks with inequations and saturation. #1004's
contracts (`T-GB`, `T-GB-conv`, `T-PT1`, `T-PTALL`) and the lineage schema's `task` field have
no saturation task, so the panel admits what those contracts can state:

- The three `-nonzero` problems add the Rabinowitsch generator t·E·F·S₀⋯S_sites − 1, encoding
  "every free species is nonzero". Their task is `T-GB` of the **augmented ideal** in
  k[species, t], labelled by a `rabinowitsch-augmentation` transformation. It is not the saturation
  I : (E·F·S₀⋯S_sites)^∞. Here the augmented `vdim` equals the parent's at both primes, so no
  steady state of these specializations has a zero free species.
- Producing the saturation itself needs an elimination order on t and an extraction step. That is
  a new contract, which #1004 would have to write before any arm could be compared on it. It is not
  admitted, and this is recorded as an exclusion rather than approximated by the augmented basis.

## Verification procedure

A successful arm output on a `p31` record is verified by comparing its `reduced-basis-v1` digest
with `references.json`. To compute that digest, make each basis element monic and normalize it the
way `normalized-input-v1` does, then hash `{format, field, variables, order, basis}`. The oracle is
Singular, `option(redSB)`, `std` then `simplify(…, 1)`, run as a subprocess.

On a `p64` record the oracle is certified grobx 0.155.1 (`8005a2a1`, `tools/external/grobx-driver`),
as the [M33 protocol](../../docs/research/adaptive-selection-contracts.md) allows above 2³¹. Its
checker independently verifies every returned basis. The tool parses grobx's basis text and computes the
same `reduced-basis-v1` digest. Making each element monic at its grevlex leading term means the two
oracles' different scalars and orderings cannot change the digest; the `p31` digests were identical
before and after that normalization was added. 36 of 39 `p64` records have a reference, and the three
frontier rows are kept with no reference.

The two fields check each other. On every problem with a reference at both primes, zero-dimensionality
and `vdim` agree between Singular at `p31` and grobx at `p64`. grobx's `vdim` is counted from the
staircase of its leading terms. `m34-public-corpus-test.py` asserts that agreement.

## Exclusions

| Upstream entries | Reason |
|---|---|
| `Cyclic_*`, `Katsura_*`, `Singular.rcyclic_*`, `Singular.ecyclic_*`, `PoSSo.rkat*`, `Verschelde.eco*`, `Verschelde.redeco*`, `Verschelde.noon*`, `Noonburg-89`, `Reimer_5` | Relatives of the existing ladders. Admitting them would need parent links to the retained Zeebra definitions (#1005 audit); they are left to that lineage work |
| `Geometry.*` with parameters, and other entries whose coefficients contain symbols | Parametric ideals over Q(u), not exact prime-field systems. A specialization would be a new formulation with its own contract |
| `Geometry.*` without parameters (135), `Curves.*`, `ZeroDim.*` | Not reviewed yet: generated test sets whose provenance needs per-entry review. Next slice |
| `satlib.*` | Boolean SAT encodings. This is a different task class from T-GB over a large prime |
| `Paris.fronville`, `Paris.safey` | 130–165 kB inputs. Deferred until the matrix budget C is fixed (owner decision 3, #1043) |
| `Amrhein`, `Czapor-86c_2`, `Meintjes`, `Singular.schwarz_6`, `ZeroDim.example_33` | Flagged by the first screen; not reviewed |
| `Cassou_1`, `Rose_1`, `FourCircles_1` | Same-size variants of admitted models. They add no scale (see *Composition hand-off*) |
| The remaining IntPS entries (`Gerdt-*`, `Wang-*`, `Czapor-*`, `Pfister_*`, `Vermeer*` and others) | Not reviewed yet. Candidates for later slices |
| `ModPS` | Systems that are already modular, at a fixed prime. Not yet reviewed |
| Saturation outputs I : g^∞ | No #1004 contract or schema `task` for them. The augmented-ideal `T-GB` is admitted instead and labelled as such (see *Inequations and saturation*) |
| Groebner.jl's Henrion, Hexapod, IPP | Not admitted. IPP's PHCpack form has decimal coefficients, which are never converted silently. No primary-source definition of Hexapod or Henrion was reconstructed within the #1006/#1007 line cap |
| BioModels steady states (BIOMD103, BIOMD123) | Rate laws must be turned into polynomials and parameters specialized from SBML. That is an export step with its own audit, not done here. `app/multisite-phosphorylation` covers the mass-action steady-state class |
| SIAN / StructuralIdentifiability.jl exports | Toolchain not installed; each export is a seeded random specialization (see sources) |
| MathRepo | No licence stated |

## Composition hand-off to #1007 (§8.2)

`composition.json` is #1006's side of the combined composition table. `catalog` writes it, and
`check` fails when it is stale. For each `family_id` it lists the base problems, the scales (the
distinct values of `n`, the variable count), the `source_id`s, a `multi_scale` flag, and the
reference-frontier rows at each field. Frontier here means the oracle did not finish, which is a
proxy. §8.2's frontier is "no arm finishes within C", and #1012 measures that. The combined table,
from `python3 tools/m34_structural_corpus.py compose`, is in
[`research/m34-structural-corpus/README.md`](../m34-structural-corpus/README.md#pilot-composition-1006--1007).

| | Base problems | Families |
|---|---:|---:|
| Whole #1006 panel | 62 | 23 |
| Families with ≥ 2 scales | 46 | 10 |
| Single-scale families | 16 | 13 |

**Second scales added.** Every `sd/*` family was checked against the pinned SymbolicData revision
for an exact entry of the same model at a different `n`. Three exist, and each is admitted:

- `Fee_2` (n = 5), of which `Fee_1` is the specialization b = 2.
- `Schiele_1` (n = 3, the half-tangent substitution) and `Schiele_1_1` (n = 2, p = 1).
- `Geometry.Heron_1` (n = 6), the same Heron area derivation in another coordinatization.

The Chandrasekhar ladder was also extended to n = 12 and 13. Both are frontier at both fields.

**Single-scale families, for the owner's waiver decision.** No exact public second scale exists for
these at the pinned revision, so none was added and none was invented.

| Family | Problems | Why there is no second scale |
|---|---:|---|
| `sd/classical/caprasse`, `czapor-86a`, `weispfenning-94`, `raksanyi`, `bjoerk_8` | 1 each | One fixed-size model, with no other entry of the model upstream. Czapor-86b and -86c are different models from the same paper, not scales of 86a |
| `sd/classical/cassou`, `rose`, `fourcircles`, `trinks` | 1, 1, 1, 2 | Upstream variants (`Cassou_1`: c → c+2; `Rose_1`; `FourCircles_1`: first equation dropped; `Trinks_1`: one generator added) have the same `n`. `Trinks_1` is admitted. The others are not, because they add no scale |
| `sd/ellipsoid` | 3 | `Ellipsoid_k` for k ∈ {2, 4, −2} all have n = 10. No other size is published |
| `sd/virasoro`, `sd/chemkin` | 1 each | Single systems in Verschelde's collection |
| `sd/four-body` | 1 | One fixed-size celestial-mechanics system |

The combined read over 127 base problems in 36 families meets every rule except this one:
13 families have one scale. The owner has two ways to resolve it:

- **Waive the two-scale rule** for single-model public families. They then enter S1, S2 and S5 and
  are left out of S3, which needs a scale ladder.
- **Leave the 16 problems out of the pilot.** The combined read is then 111 base problems in 23
  families, and 13 of them, 11.7%, are frontier. Every §8.2 rule is met. The problems stay admitted
  in this catalog either way.

No family exceeds the 15% cap. The largest #1006 family, `app/chandrasekhar-h`, has 10 problems.

## Coverage by #1009's features

These values come from `examples/feature_costs.rs --skip-solve`, run on all 124 records of this
catalog. The counting rules are `coverage()` in
[`research/1009-feature-costs/summarize.py`](../1009-feature-costs/summarize.py). They are feature
*values*, not timings. #1009's cost verdicts stay those of its own campaign over the 78 first-slice
records. Counts are records: each problem has two, and both fields give the same values.

| Question | First slice (78) | Added here (46) | Panel (124) |
|---|---:|---:|---:|
| variables `n` | 2–34 | 2–24 | 2–34 |
| wide inputs, `n > 16` | 2 | 8 | 10 |
| max degree | 2–12 | 2–12 | 2–12 |
| terms | 12–796 | 10–195 | 10–796 |
| `m > n` / `m = n` / `m < n` | 12 / 44 / 22 | 0 / 40 / 6 | 12 / 84 / 28 |
| every generator homogeneous | 2 | 0 | 2 |
| degree 2, no linear generator | 16 | 22 | 38 |
| affine-linear rank > 0 | 32 | 18 | 50 |
| a scalar substitution | 36 | 20 | 56 |
| binomials > half the generators | 6 | 12 | 18 |
| a leading monomial divisible by another | 50 | 22 | 72 |
| greedy elimination width | 1–24 | 1–22 | 1–24 |
| top-degree density | 3.3·10⁻⁵ – 1 | 1.3·10⁻⁶ – 0.4 | 1.3·10⁻⁶ – 1 |
| incidence splits, unused variable, constant generator, inconsistent linear part, all initial pairs coprime, a cap reached | 0 | 0 | 0 |

- **What the additions bring.**
  - The wide region `n > 16` goes from one problem to five: phosphorylation at 5, 6 and 7 sites,
    the 6-site nonzero presentation, and `sd-robot-jcf26`.
  - There is now a size ladder of dense square quadratics, Chandrasekhar, where every Hᵢ is coupled
    to every Hⱼ.
  - There is also a ladder whose linear conservation laws and binomial-heavy complex equations grow
    with size, phosphorylation.
- **Still uncovered by public data.**
  - No public problem splits into incidence components.
  - Only `sd-raksanyi` is homogeneous.
  - No problem has all initial pairs coprime.
  - #1007's controlled families (`zb/coupled-blocks`, `zb/toric`, …) vary these properties on
    purpose. Public applications were not bent to fill them.

`examples/feature_costs.rs` gains instantiations for 18, 21, 22 and 24 variables, so every record
in this catalog can be read. To reproduce, use a private `CARGO_TARGET_DIR`:

```sh
cargo build --release --example feature_costs
for id in $(python3 -c "import json; print(*[r['id'] for r in json.load(open('research/m34-public-corpus/catalog.json'))])"); do
  "$CARGO_TARGET_DIR"/release/examples/feature_costs --catalog research/m34-public-corpus/catalog.json \
    --id "$id" --skip-solve --batches 1 --min-batch-ms 0
done > features.jsonl
```

## Status against #1006

- **Done.**
  - Licensing review of the sources in *Sources and licensing*.
    - Admitted: SymbolicData, the Chandrasekhar H-equation and n-site phosphorylation.
    - Excluded with reasons: MathRepo, SIAN and StructuralIdentifiability exports, BioModels,
      Henrion, Hexapod and IPP.
  - 62 base problems in 23 families, 124 records. Each has an exact admission path that CI
    rebuilds.
  - References at both fields for every record except the frontier rows, which are kept with no
    reference. Zero-dimensionality and `vdim` agree across fields on every pair.
  - Inequations: three Rabinowitsch presentations under `T-GB`. Saturation is a documented
    exclusion until #1004 writes a contract for it.
  - Feature coverage, above.
  - The composition hand-off in `composition.json`, with every available second scale added.
- **Owner decision.** The single-scale waiver above, or leaving those 16 problems out of the pilot.
- **Left to later work, not blocking M34.**
  - The unreviewed SymbolicData entries in *Exclusions*.
  - The ladder relatives, which need #1005's parent links.
  - A saturation contract, which is #1004's to write.
  - A SIAN export, if a toolchain is provisioned.
