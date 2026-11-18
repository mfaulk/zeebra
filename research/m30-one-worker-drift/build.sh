#!/usr/bin/env bash
# Build m29_cost_model at every src/-touching commit between the freeze and final main,
# each from its own git archive with the instrument at origin/main (b1d8e36a).
set -u
W="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
T="${T:-/buildcache/cargo-target/zeebra-890}"
export RUSTC_WRAPPER="" CARGO_INCREMENTAL=0 TMPDIR=$T/tmp
mkdir -p "$T/tmp" "$T/bin" "$T/src"
cd "$W" || exit 1
inst=$T/m29_cost_model.rs
git show b1d8e36a:examples/m29_cost_model.rs >"$inst"
# Pre-#878 trees have no ParallelSymbolic: drop the import and the assignment (README's recipe).
python3 - "$inst" "$T/m29_cost_model.noparsym.rs" <<'PY'
import re, sys
s = open(sys.argv[1]).read()
s = s.replace(" ParallelSymbolic,", "", 1)
s, n = re.subn(r"        parallel_symbolic: if args\.workers == 1 \{\n.*?\n        \},\n", "", s, count=1, flags=re.S)
assert n == 1
open(sys.argv[2], "w").write(s)
PY
for c in "$@"; do
  [ -x "$T/bin/$c" ] && continue
  rm -rf "$T/src/$c"; mkdir -p "$T/src/$c"
  git archive "$c" | tar -x -C "$T/src/$c"
  if grep -q ParallelSymbolic "$T/src/$c/src/grobner/f4/options.rs"; then
    cp "$inst" "$T/src/$c/examples/m29_cost_model.rs"
  else
    cp "$T/m29_cost_model.noparsym.rs" "$T/src/$c/examples/m29_cost_model.rs"
  fi
  (cd "$T/src/$c" && CARGO_TARGET_DIR=$T/tgt/$c cargo build -j24 --release --locked \
    --features external-runners --example m29_cost_model) >"$T/build-$c.log" 2>&1 \
    && cp "$T/tgt/$c/release/examples/m29_cost_model" "$T/bin/$c" && echo "built $c" || echo "FAILED $c"
done
