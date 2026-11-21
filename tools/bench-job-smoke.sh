#!/usr/bin/env bash
# Nightly bench-job smoke (#969): submit -> run -> report -> verify, 2 attempts on katsura-4.
# Timing is ignored and no verdict is read; shared runners make timing meaningless. The pass-through
# reserve shim stands in for bench-reserve.sh, which needs this machine's CCD layout.
#
#   tools/bench-job-smoke.sh <sig_f4_study binary> <commit> <scratch dir, not under $HOME>
set -euo pipefail
binary="$(realpath "$1")" commit="$2" scratch="$3"
tools="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mkdir -p "$scratch"
scratch="$(realpath "$scratch")"
export ZEEBRA_BENCH_JOBS="$scratch/jobs"
export ZEEBRA_BENCH_JOB_RESERVE="$scratch/reserve-shim.sh"
printf '#!/bin/sh\n[ "$1" = run ] || exit 64\nshift 3\nexec "$@"\n' >"$ZEEBRA_BENCH_JOB_RESERVE"
chmod +x "$ZEEBRA_BENCH_JOB_RESERVE"
sha="$(sha256sum "$binary" | cut -c1-64)"
cat >"$scratch/manifest.json" <<JSON
{"schema": "bench-job-manifest-v1", "mode": "dev", "context": {"issue": 969, "agent": "nightly-smoke"},
 "arms": [{"name": "entry", "commit": "$commit", "binary": "$binary", "sha256": "$sha",
           "build": {"profile": "ci-release", "flags": "--features research-sigf4",
                     "recipe": "git archive $commit | tar -x; cargo build --profile ci-release --features research-sigf4 --example sig_f4_study"},
           "argv": ["--field", "goldilocks", "--name", "katsura-4", "--engine", "entry", "--workers", "{workers}",
                    "--wall-s", "60"]}],
 "instances": [{"name": "goldilocks/katsura-4", "params": {}}],
 "run": {"workers": [1], "cpus": "0", "repetitions": 2, "interleave": "rotate", "seeds": [0], "retries": 0,
         "limits": {"wall_seconds": 90, "kill_after_seconds": 10, "rss_bytes": null, "live_bytes": null}}}
JSON
job="$("$tools/bench-job" submit "$scratch/manifest.json" | tail -n 1)"
"$tools/bench-job" run "$job"
"$tools/bench-job" report "$job"
"$tools/bench-job" report "$job" --json >"$scratch/report.json"
python3 - "$scratch/report.json" <<'PY'
import json, sys
doc = json.load(open(sys.argv[1]))
assert doc['counts']['attempts'] == 2 and doc['counts']['statuses'] == {'ok': 2}, doc['counts']
assert doc['provenance']['stop'] == 'complete', doc['provenance']['stop']
assert [len(d) for d in doc['digests'].values()] == [1], doc['digests']
print('bench-job smoke: 2 attempts ok, one basis digest')
PY
