#!/usr/bin/env python3
"""#906 M31-I controller: #901's child runner (`m31-baseline/campaign.py` `run_one`: CCD-aligned
taskset from CPU 8, `cpu-context` before and after, frequency sampling, `timeout --signal=INT`,
`rss-guard` on the child's own comm), with the final `main` and the M31-0 freeze in one rotation.

Arms (`label:workers`); the final build is `8715c8ed`, the freeze build is #901's instrument
`5919caaa`, whose timed library is the freeze `acbaf12c`:

  f4:W   final shipping F4 (`sig_f4_study --engine f4`), W = 1, 4, 8, 16
  en:W   final opt-in entry point `grobner::f4_signature`, dispatch included, W = 1, 16
  cl:W   final signature engine with the parallel cascade (`--engine sigf4 --claim`), W = 4, 8, 16:
         the route `en:W` takes on signature-routed rows, with its stage clocks
  d1:1   final design 1 (`--engine sigf4 --workers 1`)
  zf4:16 freeze shipping F4; zd1:1 freeze design 1
  cm:16, zcm:16  MQ10 only: `m29_cost_model` at the final and the freeze (the freeze
         `sig_f4_study` has no small-prime field)
  gc:1   `certified` suite: grobx certified mode, one worker, as an external process
  ec:16  `certify` suite: the entry point with `certify_f4_output` after the timed solve
  wk:1   `census` suite: shipping F4 at one worker with `--discovery` (research-work build)

    tools/bench-reserve.sh run zb-906 8-23 python3 -u research/m31-final/campaign.py \\
        --suite walls --bins BINDIR --output OUT.jsonl
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def _module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BASE = _module('m31campaign', ROOT / 'research/m31-baseline/campaign.py')

# Plan §10.3, as pinned by #901 (`research/m31-baseline/pins.json`); eco-14 dropped by M31-0.
SIG_ROWS = ['wide64/eco-12', 'goldilocks/katsura-11', 'wide64/katsura-11', 'goldilocks/mq-random-11',
            'goldilocks/cyclic-7', 'wide64/cyclic-7', 'goldilocks/katsura-4', 'wide64/katsura-4',
            'goldilocks/noon-7', 'wide64/katsura-9', 'wide64/noon-8']
MQ10_ROWS = ['gf32003/mq-random-10', 'm31/mq-random-10']
COST_TARGET = {'gf32003/mq-random-10': 'mq10-32003', 'm31/mq-random-10': 'mq10-m31'}
FINAL_ARMS = ['f4:1', 'f4:4', 'f4:8', 'f4:16', 'en:1', 'en:16', 'cl:4', 'cl:8', 'cl:16', 'd1:1']
# grobx certified: the four wide rows M30 ran grobx on; Eco-12 at the 32 GiB cap #855 declared.
CERTIFIED_ROWS = ['wide64/eco-12', 'goldilocks/mq-random-11', 'wide64/katsura-11', 'wide64/cyclic-7']
CERTIFIED_CAP_S = 600
CERTIFIED_GIB = {'wide64/eco-12': 32}

SUITES = {
    'walls': ([(r, FINAL_ARMS + ['zf4:16', 'zd1:1']) for r in SIG_ROWS]
              + [(r, FINAL_ARMS + ['cm:16', 'zcm:16']) for r in MQ10_ROWS]),
    'certify': [(r, ['ec:16']) for r in SIG_ROWS + MQ10_ROWS],
    'census': [(r, ['wk:1']) for r in SIG_ROWS + MQ10_ROWS],
    'certified': [(r, ['gc:1']) for r in CERTIFIED_ROWS],
}
ONE_REP = {'certify', 'census'}


def command(bins, row, arm):
    label, workers = arm.split(':')
    if label in ('cm', 'zcm'):
        binary = bins['cost'] if label == 'cm' else bins['zcost']
        return 'm29_cost_model', [str(binary), '--target', COST_TARGET.get(row, row), '--workers', workers]
    if label == 'gc':
        return 'grobx-driver', [str(bins['grobx']), str(bins['requests'] / request_name(row))]
    field, name = row.split('/')
    binary = {'z': bins['zsig'], 'w': bins['work']}.get(label[0], bins['sig'])
    engine = {'f4': 'f4', 'zf4': 'f4', 'wk': 'f4', 'en': 'entry', 'ec': 'entry'}.get(label, 'sigf4')
    argv = [str(binary), '--field', field, '--name', name, '--engine', engine,
            '--workers', workers, '--wall-s', str(BASE.CAP_S)]
    if label == 'cl':
        argv.append('--claim')
    if label == 'ec':
        argv.append('--certify')
    if label == 'wk':
        argv.append('--discovery')
    return 'sig_f4_study', argv


def request_name(row):
    # rss-guard confirms its pid by this substring of the cmdline, so the row name is in the path.
    return row.replace('/', '-') + '.request'


def write_requests(directory):
    """grobx certified requests, built exactly as `research/m30-baseline/verify_wide.py` builds them."""
    scaling = _module('scaling', ROOT / 'tools/external/comparand-scaling.py')
    cases = {(c['field'], c['name']): c
             for c in json.loads((ROOT / 'research/wide-corpus/cases.json').read_text())}
    directory.mkdir(parents=True, exist_ok=True)
    out = {}
    for row in CERTIFIED_ROWS:
        case = scaling.canonical_case(cases[tuple(row.split('/'))])
        request = dict(variables=case['variables'], modulus=case['modulus'], order='grevlex', workers=1,
                       generators=case['generators'], mode='certified', wall_ns=CERTIFIED_CAP_S * 10**9,
                       rss_bytes=CERTIFIED_GIB.get(row, 8) * 1024**3)
        (directory / request_name(row)).write_text(json.dumps(request))
        out[row] = (scaling, case, request)
    return out


def certified_summary(context, row, report):
    """Admit grobx's certified answer through comparand-scaling's `certified_basis`; keep the
    digest, not the basis."""
    if report is None:
        return None
    scaling, case, request = context[row]
    try:
        basis = scaling.certified_basis(report, case, request)
    except (ValueError, KeyError) as error:
        return dict(admitted=False, error=str(error))
    return dict(admitted=True, elements=len(basis),
                basis_text_sha256=hashlib.sha256('\n'.join(sorted(basis)).encode()).hexdigest(),
                solve_ns=report.get('solve_ns'), rss_cap_gib=CERTIFIED_GIB.get(row, 8))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite', choices=sorted(SUITES), required=True)
    p.add_argument('--bins', type=Path, required=True,
                   help='directory with sig_f4_study, m29_cost_model, grobx-driver and freeze/, work/')
    p.add_argument('--reps', type=int, default=9)
    p.add_argument('--start-rep', type=int, default=0, help='resume a killed session')
    p.add_argument('--rows', help='comma-separated subset of the suite rows')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    d = args.bins
    bins = dict(sig=d / 'sig_f4_study', cost=d / 'm29_cost_model', zsig=d / 'freeze/sig_f4_study',
                zcost=d / 'freeze/m29_cost_model', work=d / 'work/sig_f4_study', grobx=d / 'grobx-driver',
                requests=args.output.parent / 'requests')
    BASE.command = command
    rows = SUITES[args.suite]
    if args.rows:
        keep = set(args.rows.split(','))
        rows = [(r, a) for r, a in rows if r in keep]
    context = write_requests(bins['requests']) if args.suite == 'certified' else None
    reps = 1 if args.suite in ONE_REP else args.reps
    with args.output.open('a') as out:
        for rep, row, arm in BASE.plan(rows, reps):
            if rep < args.start_rep:
                continue
            if args.suite == 'certified':
                BASE.CAP_S, BASE.RSS_KB = CERTIFIED_CAP_S, (CERTIFIED_GIB.get(row, 8) + 1) * 2**20
            record = dict(suite=args.suite, rep=rep, row=row, arm=arm,
                          argv=command(bins, row, arm)[1], load_start=os.getloadavg()[0],
                          # rss-guard matches `row`'s last component in the cmdline: the cost
                          # model's is its target name.
                          **BASE.run_one(bins, COST_TARGET[row] if arm.startswith(('cm', 'zcm')) else row,
                                         arm))
            if args.suite == 'certified':
                record['certified'] = certified_summary(context, row, record.pop('report'))
                record['report'] = None
                status = 'admitted' if (record['certified'] or {}).get('admitted') else f"rc={record['returncode']}"
            else:
                status = (record['report'] or {}).get('status', f"rc={record['returncode']}")
            out.write(json.dumps(record) + '\n')
            out.flush()
            print(args.suite, rep, row, arm, f"{record['process_wall_ns'] / 1e9:.3f}s", status,
                  f"load={record['load_start']:.1f}", flush=True)


if __name__ == '__main__':
    main()
