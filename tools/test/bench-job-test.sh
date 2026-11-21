#!/usr/bin/env bash
#
# The bench-job runner's unit tests, the attempt journal's, and the M31 controller that now
# imports the shared child runner — one entry for CI's agent-scripts job.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
python3 "$here/attempt-journal-test.py"
python3 "$here/bench-job-test.py"
python3 -m unittest discover -s "$here/../../research/m31-baseline" -p 'test_campaign.py'
