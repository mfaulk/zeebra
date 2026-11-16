#!/usr/bin/env bash
# #754: re-measure Zeebra's M28 cells as a serial and a 16-worker cohort.
#
# Run under the bench lock, from the checkout root, after building at the commit being stamped:
#   tools/benchlock.sh 754-m28 bash research/competitive/m28-754/run.sh
# Zeebra only: comparand rows are unchanged by #813 and stay as recorded.
set -u
: "${CARGO_TARGET_DIR:?set CARGO_TARGET_DIR to the build that was just made}"
sweep="$CARGO_TARGET_DIR/release/examples/competitive_sweep"
ZEEBRA_MACHINE="$(hostname)"
export ZEEBRA_MACHINE
log="${M28_754_LOG:-/dev/stderr}"

measure() { # workers cpus characteristic row task
    ZEEBRA_AFFINITY="$2" timeout --signal=INT --kill-after=10s 185 \
        taskset -c "$2" "$sweep" --engines zeebra --workers "$1" \
        --characteristic "$3" --row "$4" --task "$5" --wall 60 --measure --write \
        >/dev/null 2>&1
    echo "workers=$1 cpus=$2 p=$3 $4 $5 rc=$? load=$(cut -d' ' -f1 /proc/loadavg)" >>"$log"
}

for cohort in "1 2" "16 2-17"; do
    set -- $cohort
    for characteristic in 32003 2147483647; do
        for row in katsura-{4..11} cyclic-{4..9} mq-random-{6,10,14} mq-planted-{6,10,14}; do
            for task in reduced-grobner-basis lex-basis-by-conversion; do
                measure "$1" "$2" "$characteristic" "$row" "$task"
            done
        done
    done
    for row in mq-planted-wide-{6,10,14}; do
        measure "$1" "$2" 18446744073709551263 "$row" reduced-grobner-basis
    done
done
