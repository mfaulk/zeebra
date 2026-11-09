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
# All six types' toy examples are fetched since #197: the GF(2) families (I and IV) import over
# `fields::Zp2` and the GF(2^8) ones (II and V) over `fields::Gf256Mq`. The toy sizes are not the
# same per type — I, II and III publish n = 10, 15, 20 and IV, V and VI publish n = 5, 10, 15 —
# which is why the archive list below is written out rather than looped over a common range.
#
#   tools/fetch-mq-challenge.sh            # every type's toy examples; types V and VI at m=16;
#                                          # type III at n=34
#   tools/fetch-mq-challenge.sh --verify   # check the checksums of what is already there
#
set -euo pipefail

BASE="https://www.mqchallenge.org/toy-example"
CHALLENGE_BASE="https://www.mqchallenge.org/challenges"
DEST="${ZEEBRA_MQ_DIR:-research/instances/mq}"

# Checksums of the individual instance files this repository's tests and manifests name. Recorded
# so that a result can say which bytes it was computed against; the archives themselves are not
# checksummed because the site may repackage them.
# Recorded 2026-11-09 for types I, II, IV and V (#197); the type III, VI and real-challenge sums
# predate it. Every toy instance ships a companion `-answer` file — unlike the real challenges — so
# the answers checksummed here are the independent correctness oracle the tests evaluate against.
read -r -d '' CHECKSUMS <<'EOF' || true
c100943e1d9a0683e0ed8db03eade2fad52b99242a2221a3e4af4a1600cc49a9  ToyExample-type1-n10-seed0
34b710dd62543d217d60a08b7e2d7481bf1356d2f4d976e5aec0e7f9792e7d5e  ToyExample-type1-n10-seed0-answer
c4b929b2bce0a3380a0de70a26dd4f631677bd80c6253aa2eb757606b6e960d3  ToyExample-type1-n15-seed0
e2373bf100bcd3a88c89bf4b89900081c993882b76321c182cf3c7c917a03b35  ToyExample-type1-n20-seed0
1bfd90a6d45894b62a78ff72bd056f108c137fd28d11405397180c4e6790c4ae  ToyExample-type2-n10-seed0
1fae717599ff212852fe67415942e2f3d2adfec8fc968ac32b727ed92517bd0d  ToyExample-type2-n10-seed0-answer
8712976537fdb09e54ba7b85831c7f9f6ec6729897ba36df31ba66ee9633b539  ToyExample-type2-n15-seed0
e1a6426d6e9f4f4e6fb966ef623c0040331b3fb4cc387e7b340c2cb79aee9bdb  ToyExample-type2-n20-seed0
cc03c5fc6d669d683557f20ca8dd2431781cfa7de06bfbc5416ed68ff484fb14  ToyExample-type4-n5-seed0
be419a56101101c46259241432d6a8b9ea6c5d4a056fd161f3cab5ea83872f2d  ToyExample-type4-n5-seed0-answer
29b587e7d06ae2fc25d905b20747f3d82fab43bd96be70f3d62f520ac20f0231  ToyExample-type4-n10-seed0
71684e22afb96654a4c88ce6ae791b2409bc898ac05a1b28b5bcac0b5b7a8a7d  ToyExample-type4-n15-seed0
e3698bdbbcfabc3ec27c7fbf703f07ab86f47f070b16566bd7b513796a5a324f  ToyExample-type5-n5-seed0
31a690418d15efd82cfa0cf3f4a565e5b3b996ff4c10e32d220bd1d27993dbb3  ToyExample-type5-n5-seed0-answer
fb9f0b108c60a4dcbc3a4ea7e9b3343909cb8bd4b4a5c61ab53c6a2da58cb29a  ToyExample-type5-n10-seed0
712ae912e6c63911e4b04e55550b1f38d1faa0ea1cfbf7c9e6188b00ca210cd2  ToyExample-type5-n15-seed0
9436e45dbd4247f152681e954f1db19d92e8cf5e76b2bc35530bed74aae522ba  ToyExample-type3-n10-seed0
1b60acfdcc406c418cafe63e50deec23f5a8b0d29ed7701df56f9eedb4648fd8  ToyExample-type3-n10-seed0-answer
1dcee7e5e1a5dad4885471fed133158d6bce7a61822ed4aa39a1f91c9264b97b  ToyExample-type3-n15-seed0
ecb087b4128d490dd0931b877f7827786d3f49fa27facabde629d9e1f057e072  ToyExample-type3-n20-seed0
9512b6032be415ae8391b72ed8ad4f43357bafa4f0058d60b06dba3537a41af3  ToyExample-type6-n10-seed0
7d1f12bb9a09b898811805ba5979033283b9851d7cbc2b6bd276b46fa5759bdb  ToyExample-type6-n10-seed0-answer
ad22fe9a065688453b481fe8cb0e2990f3207920dc83e8c64f8dea2651b5e888  ToyExample-type6-n15-seed0
354de307fa5524d01c8a6ece3c712c27119cf3388bdd7a3e1c84095ed6cc43de  challenge-6-16-0
fb4b6a3d27fb8263b1a9883745691f3836ad747a6a4052d28919ea5b1a213cc7  challenge-5-16-0
a6f1a1626d296f68c11895bdf4d8b0948a5239feea35f1cfeb3e96a4228bd901  challenge-3-34-0
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

# The sizes the site actually publishes per type, which are not the same for all six: the
# encryption types (I, II, III) have n = 10, 15, 20 and the signature types (IV, V, VI) have
# n = 5, 10, 15. Listed rather than looped over a common range, so a missing size is a change on
# their side rather than a 404 here. Each archive holds five seeds and an answer file per seed.
ARCHIVES="
ToyExample-type1-n10.tar.bz2
ToyExample-type1-n15.tar.bz2
ToyExample-type1-n20.tar.bz2
ToyExample-type2-n10.tar.bz2
ToyExample-type2-n15.tar.bz2
ToyExample-type2-n20.tar.bz2
ToyExample-type3-n10.tar.bz2
ToyExample-type3-n15.tar.bz2
ToyExample-type3-n20.tar.bz2
ToyExample-type4-n5.tar.bz2
ToyExample-type4-n10.tar.bz2
ToyExample-type4-n15.tar.bz2
ToyExample-type5-n5.tar.bz2
ToyExample-type5-n10.tar.bz2
ToyExample-type5-n15.tar.bz2
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
#
# `challenge-3-34-0` is the smallest real *encryption* instance (type III's range starts at n = 34)
# and is far past what the solvers reach. It is fetched because it is the only evidence for one of
# the three generator classes of `docs/research/fukuoka-mq.md` §7.3 — real encryption resamples the
# value 31 and still keeps its constant column out of the stream — and
# `mq_generator::tests::test_a_published_instance_is_generated_coefficient_for_coefficient` asserts
# it. 115 kB.
CHALLENGES="
VI/challenge-6-16-0
V/challenge-5-16-0
III/challenge-3-34-0
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
