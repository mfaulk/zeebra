"""#716 summary: per-arm medians and the predeclared Gate A1 read (plan §6.1).

Gate A1: on MQ11 or Eco-12, a signature-aware arm against its comparable signature-disabled arm
(same combination policy) shows >=2x less coefficient work AND >=25% less process wall, peak RSS
<=1.5x, and identical verified output. Work is grobx's own `subtracted` charge over every run of
the call, abandoned signature runs included. Wall intervals are 95% bootstrap intervals of the
median ratio, resampling each arm independently (conservative: arms are interleaved, not paired).

    python3 research/m30-signature/summarize.py research/m30-signature/cohort.json.gz
"""
import gzip
import json
import random
import statistics
import sys
import zlib
from pathlib import Path

DRAWS = 20000
GATE_CASES = ('mq11-goldilocks', 'eco12-wide64')
PAIRS = [('default', 'sig-off'), ('no-handover', 'sig-off'),
         ('default-nocomb', 'sig-off-nocomb'), ('no-handover-nocomb', 'sig-off-nocomb')]


def interval(a, b, seed):
    rng = random.Random(seed)
    ratios = sorted(statistics.median(rng.choices(a, k=len(a))) / statistics.median(rng.choices(b, k=len(b)))
                    for _ in range(DRAWS))
    return ratios[int(0.025 * DRAWS)], ratios[int(0.975 * DRAWS) - 1]


def shape(attempt):
    """The deterministic part of a ledger: everything but clocks."""
    return [{k: v for k, v in run.items() if k not in ('stage_seconds', 'run_seconds')}
            for run in attempt['ledger']['runs']]


def cells(cohort):
    groups = {}
    for a in cohort['attempts']:
        groups.setdefault((a['case'], a['arm']), []).append(a)
    out = {}
    for (case, arm), attempts in groups.items():
        ok = [a for a in attempts if a['status'] == 'verified']
        cell = dict(case=case, arm=arm, attempts=len(attempts),
                    outcomes={s: sum(a['status'] == s for a in attempts) for s in sorted({a['status'] for a in attempts})},
                    failures=sorted({a.get('failure', '') for a in attempts if a['status'] != 'verified'}))
        if ok:
            walls = [a['process_wall_ns'] / 1e6 for a in ok]
            shapes = {json.dumps(shape(a), sort_keys=True) for a in ok}
            first = ok[0]['ledger']
            cell.update(
                n=len(ok), wall_ms=walls, wall_median_ms=statistics.median(walls),
                wall_min_ms=min(walls), wall_max_ms=max(walls),
                rss_mib_median=statistics.median(a['peak_rss_bytes'] / 2**20 for a in ok),
                rss_mib_max=max(a['peak_rss_bytes'] / 2**20 for a in ok),
                deterministic_path=len(shapes) == 1,
                answers=sorted({a['basis_text_sha256'] for a in ok}),
                subtracted_total=sorted({a['ledger']['subtracted_total'] for a in ok}),
                subtracted_discarded=sorted({a['ledger']['subtracted_discarded'] for a in ok}),
                runs=shape(ok[0]), plain_pairs=ok[0].get('plain_pairs'),
                stage_seconds_median=[{k: statistics.median(a['ledger']['runs'][i]['stage_seconds'][k] for a in ok)
                                       for k in first['runs'][i]['stage_seconds']} for i in range(len(first['runs']))],
                load_max=max(max(a['load_before'], a['load_after']) for a in ok))
        out[(case, arm)] = cell
    return out


def gate(table):
    rows = []
    for case in GATE_CASES:
        for sig, off in PAIRS:
            s, o = table.get((case, sig)), table.get((case, off))
            if not s or not o:
                continue
            row = dict(case=case, arm=sig, against=off)
            if not s.get('n') or not o.get('n'):
                row.update(complete=False, reason='an arm has no verified attempt: ' + json.dumps([s['outcomes'], o['outcomes']]))
                rows.append(row)
                continue
            work = o['subtracted_total'][0] / s['subtracted_total'][0]
            wall = s['wall_median_ms'] / o['wall_median_ms']
            lo, hi = interval(s['wall_ms'], o['wall_ms'], zlib.crc32(f'{case} {sig} {off}'.encode()))
            rss = s['rss_mib_median'] / o['rss_mib_median']
            same = s['answers'] == o['answers'] and len(s['answers']) == 1
            row.update(complete=True, work_ratio_off_over_sig=work, wall_ratio_sig_over_off=wall,
                       wall_ci95=[lo, hi], rss_ratio_sig_over_off=rss, identical_output=same,
                       deterministic_work=len(s['subtracted_total']) == 1 and len(o['subtracted_total']) == 1,
                       work_bar=work >= 2, wall_bar=wall <= 0.75, wall_bar_interval=hi <= 0.75,
                       rss_bar=rss <= 1.5)
            row['passes'] = all(row[k] for k in ('work_bar', 'wall_bar', 'wall_bar_interval', 'rss_bar', 'identical_output'))
            rows.append(row)
    return rows


def controls(table):
    """Overlay overhead and path identity: stock binary against the research binary's default."""
    rows = []
    for (case, arm), cell in sorted(table.items()):
        if arm != 'stock' or not cell.get('n'):
            continue
        d = table.get((case, 'default'))
        if not d or not d.get('n'):
            continue
        lo, hi = interval(d['wall_ms'], cell['wall_ms'], zlib.crc32(f'{case} control'.encode()))
        rows.append(dict(case=case, research_over_stock=d['wall_median_ms'] / cell['wall_median_ms'],
                         ci95=[lo, hi], same_path=d['runs'] == cell['runs'], same_answer=d['answers'] == cell['answers']))
    return rows


def main():
    path = Path(sys.argv[1])
    with gzip.open(path, 'rt') as f:
        cohort = json.load(f)
    table = cells(cohort)
    summary = dict(commit=cohort['commit'], cohort=cohort['cohort'], binaries={k: v['sha256'] for k, v in cohort['binaries'].items()},
                   attempts=len(cohort['attempts']), planned=len(cohort['attempt_plan']), refusal=cohort.get('refusal'),
                   cells=[table[k] for k in sorted(table)], gate_a1=gate(table), controls=controls(table))
    out = path.parent / (path.name.split('.')[0] + '-summary.json')
    out.write_text(json.dumps(summary, indent=1, sort_keys=True) + '\n')
    for c in summary['cells']:
        if c.get('n'):
            r = c['runs']
            print(f"{c['case']:22} {c['arm']:20} n={c['n']} wall {c['wall_median_ms']:9.1f} [{c['wall_min_ms']:.1f},{c['wall_max_ms']:.1f}] "
                  f"rss {c['rss_mib_median']:7.1f} work {c['subtracted_total'][0]/1e6:9.1f}M disc {c['subtracted_discarded'][0]/1e6:7.1f}M "
                  f"runs {'+'.join(x['engine'][0] + str(x['rounds']) for x in r)} red {sum(x['reductions'] for x in r)} "
                  f"zero {sum(x['zero_reductions'] for x in r)} zrows {sum(x['zero_rows'] for x in r)} det={c['deterministic_path']}")
        else:
            print(f"{c['case']:22} {c['arm']:20} NO VERIFIED {c['outcomes']} {c['failures']}")
    for g in summary['gate_a1']:
        print('A1', json.dumps(g))
    for c in summary['controls']:
        print('control', json.dumps(c))


if __name__ == '__main__':
    main()
