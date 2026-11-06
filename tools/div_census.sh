#!/usr/bin/env bash
#
# Count hardware integer-division instructions in the transform's monomorphizations.
#
# The acceptance criterion of #161 is the absence of an instruction, not a time, so it is checked
# the way `docs/MILESTONE-SIMD-PARALLELISM.md` §4.1 checks for `__umodti3`: disassemble the release
# artifact, split it by symbol, and count. Restricted to symbols under `zeebra::fft`, because a
# whole-binary count also sees the `div` in unrelated reductions and would not be attributable.
#
#   tools/div_census.sh target/release/examples/univariate_scaling
#
# Prints one line per matching symbol with a nonzero count, then a total.
set -euo pipefail

BINARY="${1:?path to a release artifact required}"
FILTER="${2:-zeebra::fft}"

# `-F'\t'` because objdump puts address, encoded bytes and mnemonic in three tab-separated columns
# and the byte column has a variable number of whitespace-separated words, so the mnemonic is not at
# a fixed whitespace field index.
objdump -d --demangle "$BINARY" | awk -F'\t' -v filter="$FILTER" '
    /^[0-9a-f]+ <.*>:$/ {
        if (symbol != "" && count > 0) printf "%6d  %s\n", count, symbol
        symbol = ""
        count = 0
        if (index($0, filter) > 0) {
            symbol = $0
            sub(/^[0-9a-f]+ </, "", symbol)
            sub(/>:$/, "", symbol)
            matched++
        }
        next
    }
    symbol != "" && $3 ~ /^[ ]*i?div[bwlq]?[ ]/ { count++; total++ }
    END {
        if (symbol != "" && count > 0) printf "%6d  %s\n", count, symbol
        printf "%6d  TOTAL div/idiv in %d symbols matching \"%s\"\n", total, matched, filter
    }
'
