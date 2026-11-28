#!/usr/bin/env python3
"""#1078 (M35 D): the layout census, run once per row (byte counts are deterministic).

    census.py run --study BIN --matrix BIN --out FILE [--jobs N]
    census.py table FILE

Each row runs the forced signature engine at one worker (`m34_matrix --engine sig --workers 1`,
with `--research-envelope`, which lifts the live budget to 48 GiB), so a row the shipping 512 MB budget refuses still reports
every arm's peak. Rows come from `sig_f4_study --generate` at the census commit.
"""
import argparse
import gzip
import json
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research' / '1200-m35-publication'))
import campaign  # noqa: E402

ARMS = ('baseline', 'source', 'u16', 'both')
# The shipping budget the refused case stops against (F4Options::default().max_live_bytes).
SHIPPING_LIVE_BYTES = 512 * 2**20
STRUCTURED = ('katsura-11', 'eco-12', 'cyclic-7', 'noon-9')
ROWS = ([('mq-dense-20-s20', 'm31', 'refused')]
        # The MQ generators take p < 2^63; m31 is held as `PrimeFieldElement64`, so its 16-byte entry
        # is the 64-bit storage case.
        + [(f'mq-dense-{n}-s{n}', f, 'dense') for n in (15, 18) for f in ('gf32003', 'm31')]
        + [(f'mq-random-{n}-s{n}', f, 'sparse') for n in (11, 12) for f in ('gf32003', 'm31')]
        + [(r, f, 'structured') for r in STRUCTURED for f in ('gf32003', 'm31', 'goldilocks')])


def record(row, field, study):
    argv = [study, '--field', field, '--name', row, '--generate', '--engine', 'f4', '--input-only']
    case = json.loads(subprocess.check_output(argv, text=True))
    p = int(case['modulus'])
    names = case['variables']
    equations = []
    for text in case['generators']:
        terms = {k: c % p for k, c in campaign.public.parse_integer_polynomial(text, names).items() if c % p}
        equations.append([{'exponents': list(k), 'coefficient': [str(c)]} for k, c in sorted(terms.items())])
    rec = {'schema': 'corpus-instance-v1', 'id': f'{row}@{field}',
           'field': {'characteristic': str(p), 'extension_degree': 1, 'defining_polynomial': []},
           'variables': names, 'order': 'grevlex', 'task': 'T-GB', 'equations': equations,
           'generator': {'call': [Path(study).name, *argv[1:]], 'zeebra_input_digest': case['digest']},
           'lineage': {'family_id': 'm35-d', 'formulation_id': f'm35-d/{row}', 'split': 'development',
                       'role': 'census'}}
    tools = campaign.panel_catalog.corpus_lineage
    rec['lineage']['support_id'] = tools.support_digest(rec)
    rec['normalized_input_digest'] = tools.input_digest(rec)
    return rec


def one(row, field, role, a, scratch):
    path = Path(scratch, f'{row}@{field}.json')
    try:
        rec = record(row, field, a.study)
    except subprocess.CalledProcessError as e:
        print(f'{field}/{row}: not generated ({e.returncode})', file=sys.stderr, flush=True)
        return dict(id=f'{field}/{row}', role=role, status='not-generated')
    path.write_text('[\n' + json.dumps(rec, sort_keys=True) + '\n]\n')
    out = subprocess.run([a.matrix, '--catalog', str(path), '--id', f'{row}@{field}', '--engine', 'sig',
                          '--workers', '1', '--wall-s', str(a.wall_s), '--stages',
                          '--research-envelope'],
                         capture_output=True, text=True)
    try:
        reply = json.loads(out.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        reply = {'status': 'unparsed', 'stderr': out.stderr[-400:]}
    keep = {k: reply.get(k) for k in ('status', 'call_ns', 'basis_sha256', 'peak_rss_bytes', 'layout', 'error')}
    keep['counters'] = {k: (reply.get('counters') or {}).get(k)
                        for k in ('batches', 'max_matrix_rows', 'max_matrix_columns', 'reducer_rows', 'targets')}
    print(f'{field}/{row}: {keep["status"]}', file=sys.stderr, flush=True)
    return dict(id=f'{field}/{row}', role=role, **keep)


def run(a):
    rows = [r for r in ROWS if not a.only or f'{r[1]}/{r[0]}' in a.only]
    with tempfile.TemporaryDirectory(dir=a.scratch) as scratch, ThreadPoolExecutor(a.jobs) as pool:
        results = list(pool.map(lambda r: one(*r, a, scratch), rows))
    with open(a.out, 'a' if a.only else 'w') as f:
        for r in results:
            f.write(json.dumps(r, sort_keys=True) + '\n')


def table(a):
    latest = {}
    for line in (gzip.open(a.file, "rt") if a.file.endswith(".gz") else open(a.file)):
        r = json.loads(line)
        latest[r['id']] = r
    for r in latest.values():
        c = r.get('layout')
        if r['status'] != 'complete' or not c:
            print(f'{r["id"]:28s} [{r["role"]}] {r["status"]} {r.get("error")}')
            continue
        peak = c['peak_live_bytes']
        base = peak['baseline']
        cells = ' '.join(f'{arm}={peak[arm] / base:.3f}' for arm in ARMS[1:])
        fits = ' '.join(arm for arm in ARMS if peak[arm] <= SHIPPING_LIVE_BYTES)
        print(f'{r["id"]:28s} [{r["role"]}] peak={base / 2**20:9.1f} MiB {cells} '
              f'wide={c["wide_batches"]}/{c["batches"]} cols={r["counters"]["max_matrix_columns"]} '
              f'rss={(r.get("peak_rss_bytes") or 0) / 2**20:.0f} MiB fits512=[{fits}]')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    r = sub.add_parser('run')
    r.add_argument('--study', required=True)
    r.add_argument('--matrix', required=True)
    r.add_argument('--out', required=True)
    r.add_argument('--jobs', type=int, default=8)
    r.add_argument('--only', nargs='*', help='field/row ids to rerun, appended to --out')
    r.add_argument('--wall-s', type=int, default=3600)
    r.add_argument('--scratch', default='/buildcache/cargo-target/zeebra-1078/tmp')
    t = sub.add_parser('table')
    t.add_argument('file')
    a = p.parse_args()
    {'run': run, 'table': table}[a.cmd](a)


if __name__ == '__main__':
    main()
