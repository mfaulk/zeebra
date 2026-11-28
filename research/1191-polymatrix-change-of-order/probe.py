#!/usr/bin/env python3
"""#1191 development probe: the module census and the Wiedemann route's stage clocks, per row.

    probe.py --pipeline BIN --rows wd-4-10,katsura-11 --arms probe,wiedemann [--cpu 40]
             [--wall-s 900] [--out records.jsonl]

One `examples/lex_pipeline` process per (row, arm), pinned to one CPU, one attempt each. Development
mode (`docs/guide/benchmarking.md`). A `probe` record keeps only its deterministic counts; any other
arm's clocks are single unreserved attempts.
"""
import argparse
import json
import subprocess
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pipeline', required=True)
    ap.add_argument('--rows', required=True)
    ap.add_argument('--arms', default='probe,wiedemann')
    ap.add_argument('--modulus', default='65537')
    ap.add_argument('--cpu', default='40')
    ap.add_argument('--wall-s', type=int, default=900)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    with open(args.out, 'a') as out:
        for row in args.rows.split(','):
            for arm in args.arms.split(','):
                cmd = ['taskset', '-c', args.cpu, args.pipeline, '--family', row, '--modulus',
                       args.modulus, '--arm', arm, '--budget', 'lifted', '--wall-s', str(args.wall_s)]
                try:
                    done = subprocess.run(cmd, capture_output=True, text=True,
                                          timeout=args.wall_s + 60)
                    record = json.loads(done.stdout) if done.returncode == 0 else {
                        'status': 'crashed', 'stderr': done.stderr[-400:]}
                except subprocess.TimeoutExpired:
                    record = {'status': 'timeout'}
                record.update(row=row, arm=arm, modulus=int(args.modulus), cpu=args.cpu)
                if arm == 'probe':
                    # The census is deterministic; keep its record free of clocks so it diffs.
                    record = {k: v for k, v in record.items()
                              if not k.endswith('_ns') and k not in ('peak_rss_bytes', 'cpu')}
                out.write(json.dumps(record, sort_keys=True) + '\n')
                out.flush()
                print(row, arm, record.get('status'), record.get('call_ns'), file=sys.stderr)


if __name__ == '__main__':
    main()
