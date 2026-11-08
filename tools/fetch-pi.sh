#!/usr/bin/env bash
#
# Fetch the Fukuoka MQ Challenge's `PI` digit stream into research/instances/mq/.
#
# `PI` is 200,000,000 ASCII `0`/`1` characters, and it is the whole input to the challenge's own
# coefficient generator: an instance's quadratic and linear coefficients are a function of
# `(type, n, m, seed)` and these bytes (`docs/research/fukuoka-mq.md` §7,
# `src/grobner/research/mq_generator.rs`). Fetched once, it serves all 760 published instances and
# every toy example.
#
# It is part of the challenge's own distribution and carries the same "All Rights Reserved" as the
# instance files, so like them it is **not committed to this repository**. The checksum below is
# what makes a generated instance reproducible without redistributing the data.
#
# `guidance.html` links two `utility/` archives that neither the front page nor `format.html`
# mentions. Both ship the same `PI`, byte for byte; the encryption one is fetched because it is the
# smaller, and because §7.3 records that the *generator* in both is broken and only the data is
# wanted here.
#
#   tools/fetch-pi.sh            # fetch, extract and verify
#   tools/fetch-pi.sh --verify   # check what is already there
#
set -euo pipefail

ARCHIVE_URL="https://www.mqchallenge.org/utility/CoefVerifier_enc.tar.bz2"
DEST="${ZEEBRA_MQ_DIR:-research/instances/mq}"

# Of `PI` itself, not of the archive: the site may repackage, and the stream is what is used.
PI_SHA256=58f55ded23d13c56178dbcae8803acfff03c09db4a6ae142fbcb2e31acdfbe98
PI_DIGITS=200000000

verify() {
    if [ ! -f "$DEST/PI" ]; then
        echo "missing: $DEST/PI"
        return 1
    fi
    # Length first: a truncated fetch is the failure that actually happens, and it is the one a
    # reader of a mismatching checksum would have to go and diagnose.
    local size
    size=$(wc -c < "$DEST/PI")
    if [ "$size" -ne "$PI_DIGITS" ]; then
        echo "WRONG LENGTH: $DEST/PI holds $size bytes, not $PI_DIGITS"
        return 1
    fi
    if ! echo "$PI_SHA256  $DEST/PI" | sha256sum --check --status; then
        echo "CHECKSUM MISMATCH: $DEST/PI"
        return 1
    fi
    echo "ok: PI ($PI_DIGITS digits)"
}

if [ "${1:-}" = "--verify" ]; then
    verify
    exit $?
fi

mkdir -p "$DEST"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

echo "fetching CoefVerifier_enc.tar.bz2"
curl -fsSL -o "$work/utility.tar.bz2" "$ARCHIVE_URL"
tar xjf "$work/utility.tar.bz2" -C "$work"

# The archive's layout is its own; find `PI` rather than assuming a directory name, so a repackage
# is a clear failure here instead of a confusing one later.
pi=$(find "$work" -type f -name PI -print -quit)
if [ -z "$pi" ]; then
    echo "the archive holds no file named PI; the site may have repackaged it" >&2
    exit 1
fi
cp "$pi" "$DEST/PI"

echo
verify
echo
echo "Fetched into $DEST. This file is not redistributable; keep it out of commits."
