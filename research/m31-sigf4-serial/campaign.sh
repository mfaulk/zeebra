#!/usr/bin/env bash
# #903's campaigns. Build every binary first (one `git archive` per commit, `--release --features
# research-sigf4 --example sig_f4_study`, a private CARGO_TARGET_DIR), reserve CCDs 1-2, then:
#   BINS=dir OUT=dir bash research/m31-sigf4-serial/campaign.sh corpus|heldout
# `heldout` needs binaries whose sig_f4_study instantiates 8 and 9 variables (`<sha>-ho`; the
# freeze's example stops at the corpus sizes, so katsura-9 and noon-8 panic there).
set -euo pipefail
: "${BINS:?}" "${OUT:?}"
here="$(dirname "$0")"
root="$here/../.."
ab() { "$root/tools/bench-reserve.sh" run zb-903 8-23 python3 "$here/ab.py" "$@"; }
case "${1:?suite}" in
  corpus)
    ab --arm base="$BINS/acbaf12c" --arm interreduce="$BINS/f903e087" \
      --arm bookkeeping="$BINS/56fe5fea" --arm symbolic="$BINS/f9f8a18c" \
      --out "$OUT/campaign1.jsonl" --reps 9 --cpu 8 --cap 180 \
      --rows wide64/eco-12 goldilocks/katsura-11 wide64/katsura-11 goldilocks/mq-random-11 \
        goldilocks/cyclic-7 wide64/cyclic-7 goldilocks/katsura-4 wide64/katsura-4 goldilocks/noon-7 \
        wide64/katsura-9 wide64/noon-8 ;;
  heldout)
    ab --arm base="$BINS/acbaf12c-ho" --arm interreduce="$BINS/f903e087-ho" \
      --arm bookkeeping="$BINS/56fe5fea-ho" --arm symbolic="$BINS/f9f8a18c-ho" \
      --out "$OUT/heldout.jsonl" --reps 9 --cpu 8 --cap 180 --rows wide64/katsura-9 wide64/noon-8 ;;
  *) echo "unknown suite $1" >&2; exit 2 ;;
esac
