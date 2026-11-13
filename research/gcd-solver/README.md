# Solver inputs to multivariate GCD

Issue [#658](https://github.com/mfaulk/zeebra/issues/658) is resolved by the
[call-site audit and null decision](../../docs/research/multivariate-gcd.md#8-solver-input-census-and-default-decision-658).
The audited runtime source is `778e1dc94fbb963a9a1970dde526393ffbf5bdfe`.
No production source changes were needed. [census.txt](census.txt) retains the deterministic
observation lines, runtime commit, exact test harness hash and Anemoi fixture hash.

The current solver does not call the multivariate GCD API. Twelve completed corpus solves,
three planner policies and a resultant construction have zero observed calls; a frozen
Anemoi CICO input also has zero calls in one completed F4 batch before a declared batch refusal.
That prefix is not a completed cryptanalytic solve. The three standalone GCD positive controls
verify the observer and all selectable routes. Solver root finding still uses **univariate** GCD.

Reproduce the census in this worktree:

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-658
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=''
mkdir -p "$TMPDIR"
cargo test -j4 --features research-work --test gcd_profile \
  solver_census -- --nocapture --test-threads=1 > "$CARGO_TARGET_DIR/census-test.log" 2>&1
cat "$CARGO_TARGET_DIR/census-test.log"
sed -n 's/.*CENSUS /CENSUS /p' "$CARGO_TARGET_DIR/census-test.log" \
  > "$CARGO_TARGET_DIR/census-lines.txt"
sed -n '/^CENSUS /p' research/gcd-solver/census.txt \
  > "$CARGO_TARGET_DIR/retained-census-lines.txt"
diff -u "$CARGO_TARGET_DIR/retained-census-lines.txt" "$CARGO_TARGET_DIR/census-lines.txt"
sha256sum tests/gcd_profile.rs src/grobner/f4/test-data/anemoi17-cico-n5-fcico.system
```

Check the test exit status before comparing output: an empty or truncated log is not a null
result. Source changes can legitimately alter positive-control recursion counts or solver
outcomes; the retained file is historical evidence at its declared pin. The tests assert every
solver profile is entirely zero, every positive control is nonzero and returns the expected
factor, every returned point satisfies its original equations, and the cryptanalytic prefix
actually completes one batch before refusal.

Run the full observer target with
`cargo test -j4 --features research-work --test gcd_profile`; existing CI already runs it.
No elapsed-time, RSS or speedup measurements are published, so the census uses ordinary
correctness tests without a benchmark campaign. A predictor error rate is undefined for an
empty multivariate input population; general API callers remain unprofiled.
