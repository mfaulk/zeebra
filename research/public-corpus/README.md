# Verified public polynomial families

This opt-in collection adds Eco, Noonburg and Reimer systems at **GF(32003), grevlex**, with
explicit `x1,...,xN` variable order. The generators in
[`benchmark_systems.rs`](../../src/grobner/benchmark_systems.rs) are the single mathematical
definition used by fixtures, benchmarks and all adapters. No upstream model file or engine code
is copied. The existing competitive ladder and its historical identities are unchanged.

| case | tier | variables | generator degrees | quotient dimension |
|---|---|---:|---|---:|
| public-eco-4 | CI smoke | 4 | 3,3,2,1 | 4 |
| public-noon-3 | CI smoke | 3 | 3,3,3 | 21 |
| public-reimer-3 | CI smoke | 3 | 2,3,4 | 12 |
| public-eco-8 | opt-in performance | 8 | 3,3,3,3,3,3,2,1 | 64 |
| public-noon-6 | opt-in performance | 6 | 3,3,3,3,3,3 | 717 |
| public-reimer-5 | opt-in performance | 5 | 2,3,4,5,6 | 144 |

Dimensions in this table are exact Singular build 44105 observations at this field, not claims
about real roots or all characteristics. Each complete reduced basis is committed under
[`references/`](references/), along with an input digest and raw-reference SHA-256 in
[`public_corpus_cases.rs`](../../src/grobner/external/public_corpus_cases.rs).
Ordinary unit tests recompute the three smoke bases and compare every monic coefficient, without
requiring an external executable. The larger cases are explicitly ignored unless requested.

## Definitions and provenance

- **Eco:** for `k=1,...,N-1`, `(x_k + sum_{j=1}^{N-k-1} x_j*x_{j+k})*x_N-k`, followed by
  `1+sum_{j=1}^{N-1} x_j`. This is Morgan's economics family as documented by
  [AlgebraicSolving.jl](https://algebraic-solving.github.io/examples/#Eco-n).
- **Noonburg:** `10*x_i*sum_{j != i} x_j^2 - 11*x_i + 10`, in increasing `i` order. The
  [PHCpack model entry](https://homepages.math.uic.edu/~jan/Demo/noon3.html) gives parameter
  `11/10` and cites Noonburg, SIAM J. Appl. Math. 49(6), 1989, DOI
  [10.1137/0149109](https://doi.org/10.1137/0149109). We multiply every equation by 10, which is
  invertible at the registered prime; that transformation is inside the instance digest.
  The generic generator rejects characteristics dividing 10.
- **Reimer:** `2*sum_j (-1)^(j-1)*x_j^d-1` for `d=2,...,N+1`.
  [Macaulay2's ExampleSystems documentation](https://www.macaulay2.com/doc/OLD/Macaulay2-1.20/share/doc/Macaulay2/ExampleSystems/html/_reimer5.html)
  gives the five-variable equations and identifies the PoSSo collection; the three-variable
  family is also listed in the author's
  [Buchberger selection-strategy study](https://pi.math.cornell.edu/~djp282/documents/olivetti-2018.pdf).
  This is a benchmark power-sum family; no physical model or characteristic-independent solution
  count is asserted.

These are independently written implementations of published mathematical definitions, under
Zeebra's MIT license. External GPL software runs as an oracle subprocess and contributes
mathematical answers, not implementation code. We do not treat a repository-wide license as
proof of third-party model-data provenance.

[`inventory.json`](inventory.json) pins the reviewed upstream revision
`c3e1d630fba9b2155a4c389d9022f13e0ba09218`, paths, file hashes, ordered variables where declared,
coefficient-domain qualifications and decisions. It covers the smallest main benchmark exports
for Chandra/Eco/Henrion/Noon/Reimer and biology, chemistry and classic candidates. Chandra and
Henrion's residue-like exports and model files with unresolved derivations/data terms are excluded.
The selected smaller rungs are generated from the independent definitions above; they are not
represented as byte-identical copies of those larger exports. No excluded candidate bytes enter
this repository. Original-model provenance remains unresolved for those excluded candidates.

The new regimes are coupled cubic/affine constraints (Eco), symmetric cubic coupling with a
rational parameter (Noon), and increasing-degree separated power sums (Reimer). They supplement
Cyclic, Katsura and sparse random MQ rather than supplying cryptanalytic security claims.

## API and checks

```rust
use zeebra::{grobner::external::{public_corpus, CompetitiveBoard}, MonomialOrder};
let input = public_corpus::instance(
    "public-eco-4", 32003, MonomialOrder::GradedReverseLexicographic,
).unwrap();
let board = CompetitiveBoard::new().with_corpus(public_corpus::entries());
```

Other fields/orders return `None`; a recorded reference also rejects a mutated field, ordered
variable list, generator list or order through the full instance digest. Name changes alone do not
change an ideal's digest. The Zeebra comparison adapter includes the three-variable small-prime
instantiation required by the new smoke cases.

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-public-corpus
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
mkdir -p "$TMPDIR"
cargo test --lib public_corpus
cargo test --lib public_family_tests
python3 tools/test/public-corpus-test.py
cargo build --release --example public_corpus
"$CARGO_TARGET_DIR/release/examples/public_corpus" --list
"$CARGO_TARGET_DIR/release/examples/public_corpus" --row public-noon-6 --engine zeebra
```

Root CI runs the smoke/reference/identity tests and the Python regeneration checks. Performance
cases remain manual; `cargo test --release --lib performance_bases_match_the_independent_oracle --
--ignored` runs them with the shipped defaults. Native F4 elapsed time excludes input parsing and
full-reference checking. Its self high-water snapshot follows F4; the separate process-tree guard
includes validation and output. Neither boundary is silently substituted for another.

## Regenerate references and retain a campaign

Provision Singular build 44105 and any requested comparands first, using the
[external-engine guide](../../docs/guide/external-engines.md). Build before acquiring the lock.
Reference regeneration validates all six distinct, complete answers and their input hashes before
writing any fixture. A different oracle build requires an explicit protocol update.

```sh
ZEEBRA_MACHINE=my-machine ZEEBRA_AFFINITY=0,1,2,3 \
  tools/benchlock.sh public-reference taskset -c 0-3 \
  python3 tools/external/public-corpus.py \
  --binary "$CARGO_TARGET_DIR/release/examples/public_corpus" \
  --scratch "$CARGO_TARGET_DIR/reference" --output "$CARGO_TARGET_DIR/reference.json.gz" \
  --engines singular --repeats 1 --regenerate \
  --build 'release; fat LTO; codegen-units=1; x86-64-v3'

# Rebuild after intentionally changing committed reference literals.
cargo build --release --example public_corpus
ZEEBRA_MACHINE=my-machine ZEEBRA_AFFINITY=0,1,2,3 \
  tools/benchlock.sh public-campaign taskset -c 0-3 \
  python3 tools/external/public-corpus.py \
  --binary "$CARGO_TARGET_DIR/release/examples/public_corpus" \
  --scratch "$CARGO_TARGET_DIR/campaign" --output "$CARGO_TARGET_DIR/campaign.json.gz" \
  --engines singular,zeebra,grobx --repeats 3 \
  --build 'release; fat LTO; codegen-units=1; x86-64-v3'
```

Each solver has 60 seconds/2 GiB; the complete process tree has a 185-second/2 GiB watchdog.
Every attempt is retained, including unsupported inputs, resource refusals and failures.
The campaign records canonical inputs, complete answers, tool/build identities, stage/work counts
for Zeebra, wall time and attributable memory observations. No campaign is appended to the
competitive history automatically. Tiny smoke cases remain subject to process-startup floors.
