#!/usr/bin/env python3
"""Score ParallelForward::Auto's gate against the per-batch calibration replay (#752).

  analyze-calibration.py DIR [MIN_LOWER_NONZEROS PER_WORKER MIN_ROWS_PER_WORKER MAX_WORKERS]

For every family: summed serial forward time, summed time under the gate's choice (nearest
measured worker count at or below it), the oracle best per batch, and how many batches the gate
made slower than serial.
"""
import json
import pathlib
import sys

d = pathlib.Path(sys.argv[1])
min_nnz, per_worker, min_rows, max_workers = (
    [int(x) for x in sys.argv[2:6]] if len(sys.argv) > 5 else [100_000, 25_000, 16, 16]
)


def gate(b):
    if b["lower_nonzeros"] < min_nnz:
        return 1
    return max(1, min(b["lower_nonzeros"] // per_worker, b["lower_rows"] // min_rows, max_workers))


print(f"gate: min_nnz={min_nnz} per_worker={per_worker} min_rows={min_rows} max={max_workers}")
print(f"{'family':40} {'batches':>7} {'serial ms':>10} {'gate ms':>10} {'oracle ms':>10} "
      f"{'gate x':>7} {'disp':>5} {'slower':>6}")
for path in sorted(d.glob("*.jsonl")):
    batches = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    if not batches:
        print(f"{path.stem:40} (no batches)")
        continue
    serial = gated = oracle = 0
    dispatched = slower = 0
    for b in batches:
        s = b["serial_ns"]
        times = {int(k): v for k, v in b["parallel_ns"].items()}
        times[1] = s
        w = gate(b)
        chosen = times[max(k for k in times if k <= w)]
        serial += s
        gated += chosen
        oracle += min(times.values())
        if w > 1:
            dispatched += 1
            if chosen > s:
                slower += 1
    print(f"{path.stem:40} {len(batches):7} {serial/1e6:10.2f} {gated/1e6:10.2f} {oracle/1e6:10.2f} "
          f"{serial/gated:7.2f} {dispatched:5} {slower:6}")
