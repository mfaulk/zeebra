#!/usr/bin/env bash
#
# Fetch Fukuoka MQ Challenge toy examples into research/instances/mq/.
#
# The challenge files are "COPYRIGHT (c) 2015 FUKUOKA MQ CHALLENGE All Right Reserved" with no
# stated licence, so they are **not committed to this repository**. This script fetches them and
# verifies the checksums the manifests pin, which is what makes a result reproducible without
# redistributing the data.
#
# Only the GF(31) types are fetched. Types I/IV are GF(2) and types II/V are GF(2^8), neither of
# which zeebra exports as a coefficient type yet — see `MqField` in src/grobner/research/mq.rs.
#
#   tools/fetch-mq-challenge.sh            # type III n=10,15,20 and type VI n=5,10,15
#   tools/fetch-mq-challenge.sh --verify   # check the checksums of what is already there
#
set -euo pipefail

BASE="https://www.mqchallenge.org/toy-example"
DEST="${ZEEBRA_MQ_DIR:-research/instances/mq}"

# Checksums of the individual instance files this repository's tests and manifests name. Recorded
# so that a result can say which bytes it was computed against; the archives themselves are not
# checksummed because the site may repackage them.
read -r -d '' CHECKSUMS <<'EOF' || true
9436e45dbd4247f152681e954f1db19d92e8cf5e76b2bc35530bed74aae522ba  ToyExample-type3-n10-seed0
1b60acfdcc406c418cafe63e50deec23f5a8b0d29ed7701df56f9eedb4648fd8  ToyExample-type3-n10-seed0-answer
9512b6032be415ae8391b72ed8ad4f43357bafa4f0058d60b06dba3537a41af3  ToyExample-type6-n10-seed0
7d1f12bb9a09b898811805ba5979033283b9851d7cbc2b6bd276b46fa5759bdb  ToyExample-type6-n10-seed0-answer
EOF

verify() {
    cd "$DEST"
    local failed=0
    while read -r sum name; do
        [ -z "${name:-}" ] && continue
        if [ ! -f "$name" ]; then
            echo "missing: $name"
            failed=1
        elif ! echo "$sum  $name" | sha256sum --check --status; then
            echo "CHECKSUM MISMATCH: $name"
            failed=1
        else
            echo "ok: $name"
        fi
    done <<< "$CHECKSUMS"
    return $failed
}

if [ "${1:-}" = "--verify" ]; then
    verify
    exit $?
fi

# The sizes the site actually publishes per type, which are not the same for both: type III has
# n = 10, 15, 20 and type VI has n = 5, 10, 15. Listed rather than looped over a common range, so a
# missing size is a change on their side rather than a 404 here.
ARCHIVES="
ToyExample-type3-n10.tar.bz2
ToyExample-type3-n15.tar.bz2
ToyExample-type3-n20.tar.bz2
ToyExample-type6-n5.tar.bz2
ToyExample-type6-n10.tar.bz2
ToyExample-type6-n15.tar.bz2
"

mkdir -p "$DEST"
for archive in $ARCHIVES; do
    echo "fetching $archive"
    curl -fsSL -o "$DEST/$archive" "$BASE/$archive"
    # The archives extract into a `toy_example/` directory; flatten it.
    tar xjf "$DEST/$archive" -C "$DEST" --strip-components=1
    rm -f "$DEST/$archive"
done

echo
verify
echo
echo "Fetched into $DEST. These files are not redistributable; keep them out of commits."
