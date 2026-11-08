#!/usr/bin/env bash
#
# Fetch Fukuoka MQ Challenge instances into research/instances/mq/.
#
# The challenge files are "COPYRIGHT (c) 2015 FUKUOKA MQ CHALLENGE All Right Reserved" with no
# stated licence, so they are **not committed to this repository**. This script fetches them and
# verifies the checksums the manifests pin, which is what makes a result reproducible without
# redistributing the data.
#
# The toy examples AND the two real challenges at m = 16. The generator's `n = m * 1.5` truncates,
# so m = 16 is n = 24 — the smallest published instance in any type this crate can import, and the
# reason `SUPPORTED_DIMENSIONS` reaches 24 (#454). One dimension serves two fields there: type VI is
# GF(31) and type V is GF(2^8). Real challenges ship no answer file; nobody publishes the solution
# to an open instance, so there is nothing to check a witness against but the coefficient vectors
# themselves.
#
# Types I and IV are not fetched: they are GF(2), which `MqField` still refuses by name — the field
# exists two ways and which one the importer should use is #197's decision.
#
#   tools/fetch-mq-challenge.sh            # type III n=10,15,20; type VI n=5,10,15; types V and
#                                          # VI at m=16
#   tools/fetch-mq-challenge.sh --verify   # check the checksums of what is already there
#
set -euo pipefail

BASE="https://www.mqchallenge.org/toy-example"
CHALLENGE_BASE="https://www.mqchallenge.org/challenges"
DEST="${ZEEBRA_MQ_DIR:-research/instances/mq}"

# Checksums of the individual instance files this repository's tests and manifests name. Recorded
# so that a result can say which bytes it was computed against; the archives themselves are not
# checksummed because the site may repackage them.
read -r -d '' CHECKSUMS <<'EOF' || true
9436e45dbd4247f152681e954f1db19d92e8cf5e76b2bc35530bed74aae522ba  ToyExample-type3-n10-seed0
1b60acfdcc406c418cafe63e50deec23f5a8b0d29ed7701df56f9eedb4648fd8  ToyExample-type3-n10-seed0-answer
1dcee7e5e1a5dad4885471fed133158d6bce7a61822ed4aa39a1f91c9264b97b  ToyExample-type3-n15-seed0
ecb087b4128d490dd0931b877f7827786d3f49fa27facabde629d9e1f057e072  ToyExample-type3-n20-seed0
9512b6032be415ae8391b72ed8ad4f43357bafa4f0058d60b06dba3537a41af3  ToyExample-type6-n10-seed0
7d1f12bb9a09b898811805ba5979033283b9851d7cbc2b6bd276b46fa5759bdb  ToyExample-type6-n10-seed0-answer
ad22fe9a065688453b481fe8cb0e2990f3207920dc83e8c64f8dea2651b5e888  ToyExample-type6-n15-seed0
354de307fa5524d01c8a6ece3c712c27119cf3388bdd7a3e1c84095ed6cc43de  challenge-6-16-0
fb4b6a3d27fb8263b1a9883745691f3836ad747a6a4052d28919ea5b1a213cc7  challenge-5-16-0
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

# The real challenges are plain bzip2 files rather than tarballs, and are indexed by `n` for the
# encryption types and by `m` for the signature ones: `challenge-6-16-0` is type VI, m = 16,
# seed 0, and its header says n = 24.
CHALLENGES="
VI/challenge-6-16-0
V/challenge-5-16-0
"
for challenge in $CHALLENGES; do
    name="${challenge##*/}"
    echo "fetching $challenge"
    curl -fsSL -o "$DEST/$name.bz2" "$CHALLENGE_BASE/$challenge.bz2"
    bunzip2 -f "$DEST/$name.bz2"
done

echo
verify
echo
echo "Fetched into $DEST. These files are not redistributable; keep them out of commits."
