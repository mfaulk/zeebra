#!/usr/bin/env bash
# Per-batch serial vs concurrent forward replay (#752). Run under tools/benchlock.sh.
#   run-calibration.sh BINARY OUT_DIR
# Training families fit the gate; held-out families (other primes, wider field) validate it.
set -euo pipefail
bin=$1
out=$2
mkdir -p "$out"
cpus=$(lscpu -p=CPU,CORE | grep -v '^#' | awk -F, '!seen[$2]++ {print $1}' | sed -n '3,66p' | paste -sd,)
run() {
  local split=$1 problem=$2 modulus=$3
  echo "$(date -Is) $split $problem $modulus load=$(cut -d' ' -f1 /proc/loadavg)" >>"$out/campaign.log"
  timeout 900 taskset -c "$cpus" "$bin" --problem="$problem" --modulus="$modulus" \
    --workers=2,4,8,16,32 --repeats=3 >"$out/$split-$problem-$modulus.jsonl" ||
    echo "$(date -Is) FAILED status=$? $problem $modulus" >>"$out/campaign.log"
}
run train mq-random-10 32003
run train katsura-9 32003
run train cyclic-7 32003
run heldout mq-planted-10 2147483647
run heldout katsura-8 2147483647
run heldout cyclic-8 2147483647
run heldout mq-planted-wide-10 0
run heldout katsura-10 32003
echo "$(date -Is) done" >>"$out/campaign.log"
