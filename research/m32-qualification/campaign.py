#!/usr/bin/env python3
"""#941 Gate Q controller (plan §8.2, §7.5): M31's child runner (`research/m31-baseline/campaign.py`
`run_one`: CCD-aligned taskset from CPU 8, `cpu-context` snapshots, frequency sampling, `rss-guard`
at 8 GiB) over `examples/sig_f4_study.rs`. Arms (`label:workers`), interleaved and rotated one place
per repetition:

  f4:W   conventional F4 from the head build (F2 plus the option), `--engine f4`;
  ad:W   the head build's `F4Options::graded_engine = Adaptive` through `f4_reported`,
         `--engine adaptive`: the path the option qualifies;
  m31:W  the M31 reference entry point (`measured/927-base`, `c1d93389`, timed `src/` equal to
         `8715c8ed`), `--engine entry`.

Timed suites (each read once; §10.3's precision rule alone decides an n = 12 extension block):

  dev    MQ10 (both fields) f4/ad at 1, 4, 8, 16 (T3, T5); the signature-routed rows ad/f4/m31
         at 16 (T4, T6), noon-7 (a control) also f4/ad at 1; Cyclic-7 (both fields) f4/ad at 1
         and 16 (T5); n = 9.
  small  rows under 50 ms by #934's method (`--repeat 21` on head, `--calls 20` on the reference:
         one cold call and 20 warm, the median of the warm calls per process), n = 31: katsura-4
         (both fields) f4/ad at 1 and 16; katsura-9 ad/m31 at 1, 4, 8, 16 and f4 at 16.
  held   the held-out set, f4/ad at 1, 4, 8, 16, n = 9. Read once, after the freeze and after the
         threshold re-check (`docs/research/m32-qualification.md` §2).

Untimed suite (one child per cell; the solve budget 180 s, certification 600 s beside it):

  check  per row and graded order: ad at 1, 4, 8, 16 (grevlex: every count 1–16), conventional F4
         at 1 and 16, ad certified at 16, groebner-rs at 8, Singular where the characteristic is
         below 2³¹; ad with a 1 s wall budget on the two largest rows; thread high-water on every
         ad child. (`buchberger_reference` did not finish katsura-4 in minutes, and every input it
         can finish has fewer than six variables, which the dispatch keeps on conventional F4.)

    tools/bench-reserve.sh run zb-941 8-23 python3 -u research/m32-qualification/campaign.py \\
        --suite dev --bins BINDIR --output OUT.jsonl
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SPEC = importlib.util.spec_from_file_location('m31campaign', ROOT / 'research/m31-baseline/campaign.py')
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)

W4 = [1, 4, 8, 16]
MQ10 = ['gf32003/mq-random-10', 'm31/mq-random-10']
FAVOURABLE = ['wide64/eco-12', 'goldilocks/katsura-11', 'wide64/katsura-11', 'goldilocks/mq-random-11',
              'goldilocks/noon-7', 'wide64/noon-8']
CYCLIC = ['goldilocks/cyclic-7', 'wide64/cyclic-7']
KATSURA4 = ['goldilocks/katsura-4', 'wide64/katsura-4']
KATSURA9 = ['wide64/katsura-9']
HELD_OUT = ['goldilocks/mq-random-10', 'm31/katsura-10', 'm31/eco-11']
DEV = MQ10 + FAVOURABLE + CYCLIC + KATSURA4 + KATSURA9
# The dev controls (pins.json roles): T5 reads them at 1 and 16 workers.
CONTROLS = CYCLIC + KATSURA4 + ['goldilocks/noon-7']
NARROW = {'gf32003', 'm31'}
SOLVE_S = 180
CERTIFY_S = 600


def pairs(labels, workers):
    return [f'{a}:{w}' for w in workers for a in labels]


def check_arms(row, order):
    field = row.split('/')[0]
    counts = range(1, 17) if order == 'grevlex' else W4
    arms = [f'ad.{order}:{w}' for w in counts]
    arms += [f'f4.{order}:1', f'f4.{order}:16', f'adc.{order}:16', f'rs.{order}:8']
    if field in NARROW:
        arms.append(f'sg.{order}:1')
    if order == 'grevlex' and row in ('wide64/eco-12', 'goldilocks/mq-random-11'):
        arms += ['adw.grevlex:1', 'adw.grevlex:16']
    return arms


SUITES = {
    'dev': [(r, pairs(('f4', 'ad'), W4)) for r in MQ10]
    + [(r, pairs(('ad', 'f4', 'm31'), [16]) + (pairs(('f4', 'ad'), [1]) if r in CONTROLS else []))
       for r in FAVOURABLE]
    + [(r, pairs(('f4', 'ad'), [1, 16])) for r in CYCLIC],
    'small': [(r, pairs(('f4', 'ad'), [1, 16])) for r in KATSURA4]
    + [(r, pairs(('ad', 'm31'), W4) + ['f4:16']) for r in KATSURA9],
    'held': [(r, pairs(('f4', 'ad'), W4)) for r in HELD_OUT],
    'check': [(r, check_arms(r, o)) for o in ('grevlex', 'grlex') for r in DEV + HELD_OUT],
}
REPS = {'dev': 9, 'small': 31, 'held': 9, 'check': 1}
WARM = {'small'}
ENGINES = {'f4': 'f4', 'ad': 'adaptive', 'adc': 'adaptive', 'adw': 'adaptive', 'm31': 'entry',
           'rs': 'groebner-rs', 'sg': 'singular', 'bb': 'reference'}


def command(bins, row, arm, warm=False):
    label, workers = arm.split(':')
    label, _, order = label.partition('.')
    field, name = row.split('/')
    binary = bins['m31'] if label == 'm31' else bins['head']
    wall = 1 if label == 'adw' else SOLVE_S
    argv = [str(binary), '--field', field, '--name', name, '--engine', ENGINES[label],
            '--workers', workers, '--wall-s', str(wall)]
    if order:
        argv += ['--order', order]
    if label == 'adc':
        argv.append('--certify')
    if label in ('ad', 'adc', 'adw') and order:
        argv.append('--sample-threads')
    if warm:
        argv += ['--calls', '20'] if label == 'm31' else ['--repeat', '21']
    return 'sig_f4_study', argv


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite', choices=sorted(SUITES), required=True)
    p.add_argument('--bins', type=Path, required=True, help='directory holding {head,m31}/sig_f4_study')
    p.add_argument('--reps', type=int, help='override the suite default (the n = 12 extension)')
    p.add_argument('--first-rep', type=int, default=0, help='numbering for an extension block')
    p.add_argument('--rows', nargs='*', help='restrict to these rows (an extension block)')
    p.add_argument('--arms', nargs='*', help='restrict to these arms (an extension block)')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    bins = dict(head=args.bins / 'head/sig_f4_study', m31=args.bins / 'm31/sig_f4_study')
    warm = args.suite in WARM
    if args.suite == 'check':
        BASE.CAP_S = SOLVE_S + CERTIFY_S
    BASE.command = lambda b, row, arm: command(b, row, arm, warm)
    rows = [(r, [a for a in arms if not args.arms or a in args.arms]) for r, arms in SUITES[args.suite]
            if not args.rows or r in args.rows]
    with args.output.open('a') as out:
        for rep, row, arm in BASE.plan([x for x in rows if x[1]], args.reps or REPS[args.suite]):
            rep += args.first_rep
            record = dict(suite=args.suite, rep=rep, row=row, arm=arm,
                          argv=command(bins, row, arm, warm)[1], load_start=os.getloadavg()[0],
                          **BASE.run_one(bins, row, arm))
            out.write(json.dumps(record) + '\n')
            out.flush()
            status = (record['report'] or {}).get('status', f"rc={record['returncode']}")
            print(args.suite, rep, row, arm, f"{record['process_wall_ns'] / 1e9:.3f}s", status,
                  f"load={record['load_start']:.1f}", flush=True)


if __name__ == '__main__':
    main()
