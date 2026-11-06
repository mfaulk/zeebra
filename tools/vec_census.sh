#!/usr/bin/env bash
#
# Count vector integer instructions in a release artifact, as a check that the ISA floor survived.
#
# Why this exists, and it is not the reason #244 was filed. That issue reported the 4-byte kernel
# losing autovectorization "depending on how cargo build is invoked", measured as 91 vector
# multiplies in one artifact and zero in another from the same commit. The invocation was a
# coincidence. The real variable is whether `RUSTFLAGS` was set in that shell:
#
#   cargo build --release                           -> -C target-cpu=x86-64-v3   (from .cargo/config.toml)
#   RUSTFLAGS="-D warnings" cargo build --release    -> no target-cpu at all
#   RUSTFLAGS="" cargo build --release               -> no target-cpu at all
#
# `RUSTFLAGS` REPLACES `target.*.rustflags` rather than adding to it, so setting it for any reason
# silently drops the AVX2 floor. `docs/MILESTONE-SIMD-PARALLELISM.md` §3.1 records this trap costing
# a silent regression in CI once already, and `.cargo/config.toml` warns about it in a comment. It
# then cost #185 a crossover constant and #231 a whole set of figures, because both were measured in
# shells that set `RUSTFLAGS`.
#
# A 4-byte Montgomery multiply vectorizes and an 8-byte one does not — a 32-bit reduction is 64-bit
# arithmetic LLVM can put in a lane, a 64-bit one is 128-bit arithmetic it cannot
# (`MILESTONE-SIMD-PARALLELISM.md` §8.3). So the presence of vector multiplies in an artifact that
# exercises a 4-byte field is the signal that the floor is there, and their absence is the signal
# that it is not.
#
#   tools/vec_census.sh target/release/examples/multiplication_dispatch
#   tools/vec_census.sh target/release/examples/univariate_scaling --require
#
# `--require` exits nonzero when no vector multiply is found, which is what a CI step or a
# measurement script wants before it records a figure.
#
# Deliberately whole-artifact and not filtered by symbol, unlike `tools/div_census.sh`: under
# `lto = "fat"` with `codegen-units = 1` the polynomial kernels are inlined into their callers and
# no symbol named for them survives, so a symbol filter finds nothing and reports a false negative.
set -euo pipefail

BINARY="${1:?path to a release artifact required}"
REQUIRE="${2:-}"

if [ ! -f "$BINARY" ]; then
    echo "not a file: $BINARY" >&2
    exit 2
fi

# Vector integer classes, counted separately because they say different things. A multiply is the
# one that matters for the field arithmetic; adds and shifts alone appear even at the baseline ISA
# and are not evidence of the floor.
objdump -d "$BINARY" | awk -F'\t' '
    NF >= 3 {
        split($3, words, " ")
        mnemonic = words[1]
        if (mnemonic ~ /^vpmul/)                       { mul++;   seen[mnemonic]++ }
        else if (mnemonic ~ /^vpadd|^vpsub/)           { addsub++ }
        else if (mnemonic ~ /^vpsrl|^vpsll|^vpsra/)    { shift++ }
        else if (mnemonic ~ /^v/)                      { other++ }
    }
    END {
        printf "vector multiplies : %d\n", mul + 0
        for (m in seen) printf "    %-12s %d\n", m, seen[m]
        printf "vector add/sub    : %d\n", addsub + 0
        printf "vector shifts     : %d\n", shift + 0
        printf "other vector ops  : %d\n", other + 0
        exit (mul + 0) > 0 ? 0 : 1
    }
' && FOUND=0 || FOUND=1

if [ "$FOUND" -ne 0 ]; then
    echo
    echo "NO VECTOR MULTIPLY FOUND."
    echo "If this artifact exercises a 4-byte field, the ISA floor is probably missing. Check that"
    echo "the build did not set RUSTFLAGS; if it must, repeat the flag:"
    echo
    echo "    RUSTFLAGS=\"-D warnings -C target-cpu=x86-64-v3\" cargo build --release"
    echo
    if [ "$REQUIRE" = "--require" ]; then
        exit 1
    fi
fi
