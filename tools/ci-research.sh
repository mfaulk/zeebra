#!/usr/bin/env bash
# One CI research set per invocation. Each feature set recompiles the whole crate, so CI runs every
# set on its own runner (#922); tools/test/ci-research-test.sh holds a set to its own feature.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

SETS=(default delayed-reduction comparand-replay research-work research-multirow research-sigf4
    research-sigf4-replay research-sigf4-split research-sigf4-usage research-reuse research-adjacent)

usage() {
    printf 'usage: %s --sets | <set>\nsets: %s\n' "$0" "${SETS[*]}" >&2
    exit 2
}

[[ $# -eq 1 ]] || usage
if [[ "$1" == --sets ]]; then
    printf '%s\n' "${SETS[@]}"
    exit 0
fi

set -x
case "$1" in
    default)
        cargo test --example mq10_profile
        cargo test --example batch_order_study
        cargo test --example wide_corpus
        cargo test --example public_corpus
        cargo test --example elimination_kernel_study
        cargo test --example row_merge_study
        cargo test --test stage_refinements
        # The artifact checks below replay committed records and build nothing.
        python3 tools/test/wide-corpus-test.py
        python3 tools/test/comparand-scaling-test.py
        python3 tools/test/elimination-kernel-study-test.py
        python3 research/elimination-kernels/summarize.py
        git diff --exit-code -- research/elimination-kernels/summary.json research/elimination-kernels/curves.csv
        python3 tools/test/row-merge-study-test.py
        python3 tools/test/batch-splitting-study-test.py
        python3 tools/test/mq10-profile-test.py
        python3 tools/test/whole-route-study-test.py
        python3 tools/test/whole-route-summary-test.py
        python3 research/m28-current-baseline/summarize.py --check
        python3 tools/test/symbolic-live-study-test.py
        python3 tools/external/symbolic-live-study.py --replay research/symbolic-live
        python3 tools/test/msolve-count-test.py
        python3 tools/test/grobx-trajectory-test.py
        python3 tools/test/grobx-work-study-test.py
        python3 tools/test/pivot-discovery-study-test.py
        python3 research/concurrent-pivots/summarize.py
        python3 -m unittest discover -s research/waiting-row -p 'test_*.py'
        evidence="$(mktemp)"
        python3 research/waiting-row/evidence.py > "$evidence"
        diff -u research/waiting-row/evidence.json "$evidence"
        git diff --exit-code -- research/concurrent-pivots/summary.json research/concurrent-pivots/matrix-census.csv research/concurrent-pivots/parallel.csv research/concurrent-pivots/matrix-scaling.csv research/concurrent-pivots/dispatch.csv research/concurrent-pivots/controls.csv
        python3 tools/test/grobx-randomization-test.py
        python3 tools/external/grobx-driver/research/randomization/test_policy.py
        python3 tools/external/grobx-driver/research/signature/test_overlay.py
        python3 tools/test/grobx-signature-study-test.py
        python3 tools/test/proof-artifacts-test.py
        python3 tools/test/attempt-journal-test.py
        python3 research/grobx-randomization/summarize.py
        git diff --exit-code -- research/grobx-randomization/summary.json research/grobx-randomization/summary.csv
        python3 research/grobx-trajectory/summarize.py
        git diff --exit-code -- research/grobx-trajectory/summary.json research/grobx-trajectory/summary.csv research/grobx-trajectory/summary-rounds.csv
        python3 research/symbolic-attribution/summarize.py | diff - research/symbolic-attribution/totals.tsv
        python3 tools/test/worker-pool-study-test.py
        python3 research/worker-pool/summarize.py
        git diff --exit-code -- research/worker-pool/summary.json research/worker-pool/summary.csv
        python3 tools/test/gcd-size-study-test.py
        python3 research/gcd-size/summarize.py
        git diff --exit-code -- research/gcd-size/summary.json research/gcd-size/summary.csv research/gcd-size/table.md
        python3 tools/test/selective-backward-study-test.py
        python3 tools/test/candidate-adoption-summary-test.py
        python3 tools/test/residual-backward-model-test.py
        python3 research/residual-backward/model.py --check
        python3 research/candidate-adoption/summary.py --check
        python3 tools/test/selective-backward-summary-test.py
        python3 tools/test/selective-backward-cross-test.py
        python3 tools/test/selective-backward-combined-summary-test.py
        python3 research/selective-backward/combined_summary.py
        git diff --exit-code -- research/selective-backward/combined-summary.json
        python3 research/selective-backward/summarize.py
        git diff --exit-code -- research/selective-backward/summary.json research/selective-backward/native.csv research/selective-backward/inventory.json
        python3 research/m30-sigf4/test_run.py
        python3 research/m30-sigf4/summarize.py research/m30-sigf4/{gate,controls,gate2,controls2}.jsonl.gz | diff - research/m30-sigf4/tables.md
        python3 research/m30-final/test_campaign.py
        python3 research/m31-baseline/test_campaign.py
        python3 research/m31-baseline/summarize.py research/m31-baseline/walls.jsonl.gz research/m31-baseline/split.jsonl.gz | diff - research/m31-baseline/tables.md
        python3 research/m30-final/summarize.py research/m30-final | diff - research/m30-final/tables.md
        python3 research/m31-final/test_campaign.py
        python3 research/m31-final/summarize.py research/m31-final | diff - research/m31-final/tables.md
        python3 research/m32-baseline/test_pins.py
        python3 research/m32-baseline/summarize.py research/m32-baseline | diff - research/m32-baseline/tables.md
        python3 tools/test/multirow-study-test.py
        python3 tools/test/public-corpus-test.py
        ;;
    delayed-reduction)
        git apply research/elimination-kernels/delayed.patch
        trap 'git apply -R research/elimination-kernels/delayed.patch' EXIT
        cargo test --example elimination_kernel_study
        cargo test --lib h13_pilot_selection_is_explicit
        ;;
    comparand-replay)
        # About 12 minutes; it reads only its own records and tools/external/ (tools/ci-scope.sh).
        python3 tools/external/comparand-scaling.py --replay research/comparand-scaling
        ;;
    research-work)
        cargo test --features research-work --test symbolic_live
        cargo test --features research-work --example symbolic_attribution
        cargo test --features research-work --example worker_pool_study
        cargo test --features research-work --example parallel_forward_study
        cargo test --features research-work --lib dispatch_tests
        cargo test --features research-work --lib linalg::work
        cargo test --features research-work --test gcd_profile
        cargo test --features research-work --lib gcd_profile
        cargo test --features research-work --lib linalg::concurrent
        cargo test --features research-work --lib linalg::selective
        cargo test --features research-work --example mq10_profile
        ;;
    research-multirow)
        cargo test --features research-multirow --lib linalg::dense::band
        cargo test --features research-multirow --example mq10_profile
        ;;
    research-sigf4)
        cargo test --features research-sigf4 --lib grobner::sigf4
        cargo test --features research-sigf4 --example sig_f4_study
        ;;
    research-sigf4-replay)
        cargo test --features research-sigf4-replay --lib grobner::sigf4::replay
        cargo test --features research-sigf4-replay --example sig_f4_study
        ;;
    research-sigf4-split)
        cargo test --features research-sigf4-split --lib grobner::sigf4
        cargo test --features research-sigf4-split --example sig_f4_study
        ;;
    research-sigf4-usage)
        cargo test --features research-sigf4-usage --lib grobner::sigf4::usage
        cargo test --features research-sigf4-usage --example sig_f4_study
        ;;
    research-reuse)
        cargo test --features research-reuse --lib grobner::reuse_census
        cargo test --features research-reuse --example reuse_census
        python3 research/1031-reuse-census/summarize.py research/1031-reuse-census/runs.jsonl.gz | diff - research/1031-reuse-census/tables.md
        ;;
    research-adjacent)
        cargo test --features research-adjacent --lib grobner::sigf4::adjacent
        cargo test --features research-adjacent --example reuse_census
        python3 research/1075-adjacent-reuse/summarize.py research/1075-adjacent-reuse/runs.jsonl.gz | diff - research/1075-adjacent-reuse/tables.md
        ;;
    *)
        set +x
        usage
        ;;
esac
