"""§8.6: one record per attempt of one bench-job job.

Usage: python3 -I extract.py --job <job dir> --out <records.jsonl.gz>
"""
import argparse
import gzip
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import calib  # noqa: E402


def read(paths):
    out = []
    for p in paths:
        out += [json.loads(line) for line in gzip.open(p, 'rt')]
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--job', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    recs = calib.records(a.job)
    a.out.write_bytes(gzip.compress(''.join(json.dumps(r, sort_keys=True) + '\n' for r in recs).encode(), mtime=0))
    print(a.out, len(recs), 'attempts')


if __name__ == '__main__':
    main()
