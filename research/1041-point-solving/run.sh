#!/usr/bin/env bash
# #1041: every predeclared instance, one solve per fresh process, one at a time.
#
#   cargo build --release --example point_solving_screen
#   research/1041-point-solving/run.sh > research/1041-point-solving/measured.jsonl
#
# Per (family, size, seed): the pipeline, then hybrid branches (one correct, one wrong) for
# k = 1, 2 extra fixed variables over GF(31) and k = 1..4 over GF(2). For n > m the branch fixes
# n − m + k variables. Calibration runs before and after. A size whose pipeline does not complete
# skips its branches.
set -euo pipefail
bin="${CARGO_TARGET_DIR:-target}/release/examples/point_solving_screen"
wall="${ZB_WALL_S:-600}"
"$bin" --mode calibrate | tr -d '\n'; echo
for spec in \
  "A 31 6 12" "A 31 8 16" "A 31 10 20" "A 31 12 24" "A 31 14 28" "A 31 16 32" "A 31 18 36" \
  "B 31 6 4" "B 31 9 6" "B 31 12 8" "B 31 15 10" \
  "C 2 8 16" "C 2 12 24" "C 2 16 32" "C 2 20 40" "C 2 24 48" "C 2 28 56" \
  "D 2 12 8" "D 2 18 12" "D 2 24 16" "D 2 30 20"; do
  read -r family q n m <<<"$spec"
  base=$(( n > m ? n - m : 0 ))
  ks=$([ "$q" = 2 ] && echo "1 2 3 4" || echo "1 2")
  for seed in 1 2; do
    line="$("$bin" --q "$q" --n "$n" --m "$m" --seed "$seed" --wall-s "$wall" | tr -d '\n')"
    echo "{\"family\":\"$family\",${line#\{}"
    case "$line" in *'"status": "point"'*|*'"status": "attempts"'*) ;; *) continue ;; esac
    case "$line" in *'"status": "stopped"'*|*'"status": "refused"'*) continue ;; esac
    for k in $ks; do
      fix=$(( base + k ))
      [ "$fix" -lt "$n" ] || continue
      for b in correct wrong; do
        out="$("$bin" --q "$q" --n "$n" --m "$m" --seed "$seed" --mode branch --fix "$fix" \
          --branch "$b" --wall-s "$wall" | tr -d '\n')"
        echo "{\"family\":\"$family\",\"k\":$k,${out#\{}"
      done
    done
  done
done
"$bin" --mode calibrate | tr -d '\n'; echo
