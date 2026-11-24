#!/usr/bin/env python3
"""#1011 M34 G2: untimed correctness qualification of the portfolio arms on Z0.

    campaign.py run --harness BIN [--arms ...] [--wall-s S]   # one fresh process per cell -> results/correctness.jsonl
    campaign.py summarize                                     # verdicts per arm and field -> results/correctness.md

Every cell compares the arm's `m33-basis-v1` digest with an independent reference: M33-Q's
`research/m33-qualification/references.json`, which is Singular `std`/`redSB` below 2^31 and
groebner-rs at one worker on the wide fields. The cell's input digest must equal the input that the
reference was computed from. Nothing here is timed. A cell is a solve under the harness's wall
budget, run wherever the caller pins it; no wall or memory figure is read from these records.
"""
import argparse
import importlib.util
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FIELDS = ('gf32003', 'm31', 'w59', 'wide64', 'goldilocks')
ORDERS = ('grevlex', 'grlex', 'lex')
RESULTS = HERE / 'results' / 'correctness.jsonl'

# docs/research/adaptive-selection-contracts.md §5, plus #997's candidate W. `engine` is the harness's
# `--engine` (examples/m33_qualify.rs). Arms whose name fixes no worker count run at 1 and 16.
ARMS = {
    'P1 conv-w1': dict(engine='f4', workers=[1], family='conventional'),
    'P2 conv-w4': dict(engine='f4', workers=[4], family='conventional'),
    'P3 conv-w16': dict(engine='f4', workers=[16], family='conventional'),
    'P4 sig-w1': dict(engine='sig', workers=[1], family='signature'),
    'P5 sig-w8': dict(engine='sig', workers=[8], family='signature'),
    'P6 sig-w16': dict(engine='sig', workers=[16], family='signature'),
    'P7 conv-cap16': dict(engine='cap16', workers=[1, 16], family='cap16'),
    'P8 adaptive': dict(engine='adaptive', workers=[1, 16], family='adaptive'),
    '#997 fewest-fl': dict(engine='fewest-fl', workers=[1, 16], family='fewest-fl'),
}


def _m33q():
    spec = importlib.util.spec_from_file_location('m33q', ROOT / 'research/m33-qualification/campaign.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def key(r):
    return f"{r['order']}/{r['field']}/{r['name']}"


def references():
    return json.loads((ROOT / 'research/m33-qualification/references.json').read_text())


def rows():
    """M33-Q's correctness rows (`grevlex`, `grlex`, `lex` suites) on #1011's five fields."""
    m33q = _m33q()
    out = []
    for suite in ORDERS:
        out += [r for r in m33q.suite_rows(suite) if r['field'] in FIELDS and r not in out]
    return out


def expect(arm, r):
    """The forced signature engine refuses every order but grevlex (`SigF4Error::Unsupported`;
    graded-lex since #1049, which is what makes it ineligible under #961)."""
    return 'refused' if ARMS[arm]['family'] == 'signature' and r['order'] != 'grevlex' else 'basis'


def plan(rs, arms=None):
    return [dict(arm=a, workers=w, row=r, expect=expect(a, r))
            for r in rs for a in (arms or ARMS) for w in ARMS[a]['workers']]


def verdict(cell, record, ref_digest, ref_input):
    if record is None:
        return 'FAIL crashed'
    if record.get('digest') != ref_input:
        return 'FAIL input'
    status = record.get('status')
    if cell['expect'] == 'refused':
        if status == 'refused' and 'Unsupported' in (record.get('error') or ''):
            return 'pass (refused)'
        return 'FAIL not refused'
    if status == 'refused':
        return 'FAIL refused'
    if status == 'stopped':
        return 'stopped'
    return 'pass' if record.get('basis_m33') == ref_digest else 'FAIL digest'


def cell_id(cell):
    return f"{cell['arm']}|{cell['workers']}|{key(cell['row'])}"


def run(args):
    refs = references()
    done = set()
    if RESULTS.exists():
        done = {json.loads(x)['cell'] for x in RESULTS.read_text().splitlines()}
    RESULTS.parent.mkdir(parents=True, exist_ok=True)
    cells = [c for c in plan(rows(), args.arms) if cell_id(c) not in done]
    print(f'{len(cells)} cells to run', flush=True)
    for c in cells:
        r = c['row']
        argv = [args.harness, '--field', r['field'], '--name', r['name'], '--order', r['order'],
                '--engine', ARMS[c['arm']]['engine'], '--workers', str(c['workers']), '--wall-s', str(args.wall_s)]
        if r['catalog']:
            argv.append('--catalog')
        try:
            p = subprocess.run(argv, capture_output=True, text=True, timeout=args.wall_s + 120)
            record = json.loads(p.stdout.strip().splitlines()[-1]) if p.returncode == 0 and p.stdout.strip() else None
            failure = None if record else f'rc {p.returncode}: {p.stderr.strip()[-400:]}'
        except subprocess.TimeoutExpired:
            record, failure = None, 'harness timeout'
        ref = refs[key(r)]
        v = verdict(c, record, ref['basis_m33'], ref['input_digest'])
        keep = {k: record.get(k) for k in ('status', 'error', 'route', 'team', 'basis_m33', 'basis_elements',
                                           'digest')} if record else None
        line = dict(cell=cell_id(c), arm=c['arm'], workers=c['workers'], **r, expect=c['expect'], verdict=v,
                    reference=ref['reference'], record=keep, failure=failure)
        with RESULTS.open('a') as f:
            f.write(json.dumps(line, sort_keys=True) + '\n')
        print(c['arm'], c['workers'], key(r), v, flush=True)


def summarize(_args):
    lines = [json.loads(x) for x in RESULTS.read_text().splitlines()]
    table = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
    for x in lines:
        table[x['arm']][x['field']][x['verdict'].split(' ')[0]] += 1
    out = ['| Arm | ' + ' | '.join(FIELDS) + ' |', '|---|' + '---|' * len(FIELDS)]
    for arm in ARMS:
        if arm not in table:
            continue
        cells = []
        for f in FIELDS:
            c = table[arm][f]
            cells.append(', '.join(f'{k} {v}' for k, v in sorted(c.items())) or '—')
        out.append(f'| {arm} | ' + ' | '.join(cells) + ' |')
    bad = [x for x in lines if x['verdict'].startswith(('FAIL', 'stopped'))]
    out += ['', f'{len(lines)} cells; not passed:' if bad else f'{len(lines)} cells; every cell passed.']
    out += [f"- {x['arm']} w={x['workers']} {x['order']}/{x['field']}/{x['name']}: {x['verdict']}"
            f" ({(x['record'] or {}).get('error') or x['failure'] or ''})" for x in bad]
    (HERE / 'results' / 'correctness.md').write_text('\n'.join(out) + '\n')
    print('\n'.join(out))


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('run', 'summarize'))
    p.add_argument('--harness')
    p.add_argument('--arms', nargs='*', choices=list(ARMS))
    p.add_argument('--wall-s', type=int, default=180)
    args = p.parse_args(argv)
    if args.command == 'run':
        if not args.harness:
            sys.exit('run needs --harness')
        run(args)
    else:
        summarize(args)


if __name__ == '__main__':
    main()
