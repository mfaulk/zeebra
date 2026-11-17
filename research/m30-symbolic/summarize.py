#!/usr/bin/env python3
"""#859: tables for docs/research/m30-symbolic-cost-model.md from the retained campaign files.

    python3 research/m30-symbolic/summarize.py research/m30-symbolic > research/m30-symbolic/tables.md

Walls are medians with a 95% bootstrap interval of the median. Stage shares are formed per run
(symbolic over the same run's F4 total) and then their median is taken, because a ratio survives a
load drift between runs that absolutes do not. Replay figures sum a run's batches and take the
median across runs. Every attempt is in the input files, failures included.
"""
import gzip
import json
import random
import statistics
import sys
from pathlib import Path

TARGETS = ('mq10-32003', 'mq10-m31', 'eco12-wide64', 'mq11-goldilocks', 'katsura11-m31')
WORKERS = (1, 4, 8, 16)
DRAWS = 20000
GAIN = 0.10


def jsonl(path):
    gz = path.with_name(path.name + '.gz')
    text = path.read_text() if path.exists() else gzip.decompress(gz.read_bytes()).decode() if gz.exists() else ''
    return [json.loads(l) for l in text.splitlines() if l.strip()]


def med(xs):
    return statistics.median(xs) if xs else None


def ci(xs, seed=859):
    """95% bootstrap interval of the median."""
    rng = random.Random(seed)
    meds = sorted(statistics.median(rng.choices(xs, k=len(xs))) for _ in range(DRAWS))
    return meds[int(0.025 * DRAWS)], meds[int(0.975 * DRAWS) - 1]


def needed_speedup(f, gain=GAIN):
    """Stage speedup s with f(1 - 1/s) = gain, or None when even s = infinity falls short."""
    return None if f <= gain else 1 / (1 - gain / f)


def ok(r):
    return r['report'] is not None and r['report'].get('status', 'complete') == 'complete'


def cells(records, **keys):
    return [r for r in records if all(r[k] == v for k, v in keys.items())]


def walls(records, out):
    out.append('## Process wall, stage clocks off (ms, median [95% CI], n)\n')
    out.append('| Target | ' + ' | '.join(f'{w} worker{"s" if w > 1 else ""}' for w in WORKERS) + ' | peak RSS 16w MiB |')
    out.append('|---|' + '---:|' * (len(WORKERS) + 1))
    for t in TARGETS:
        row = []
        for w in WORKERS:
            rs = cells(records, target=t, workers=w)
            xs = [r['process_wall_ns'] / 1e6 for r in rs if ok(r)]
            if not xs:
                row.append('—')
                continue
            lo, hi = ci(xs)
            fail = len(rs) - len(xs)
            row.append(f'{med(xs):.1f} [{lo:.1f}, {hi:.1f}] n={len(xs)}' + (f' ({fail} failed)' if fail else ''))
        rss = [r['report']['peak_rss_bytes'] / 2**20 for r in cells(records, target=t, workers=16) if ok(r)]
        out.append(f'| {t} | ' + ' | '.join(row) + (f' | {med(rss):.0f} |' if rss else ' | — |'))
    out.append('')


def shares(stage_records, wall_records, out):
    out.append('## Symbolic share and the Amdahl ceiling\n')
    out.append('*f* is the symbolic stage over the same run\'s F4 total (stage clocks on), median over runs '
               '[min, max]; *f*<sub>wall</sub> divides the median clocked symbolic stage by the median '
               'unclocked process wall. *s*<sub>10%</sub> is the stage speedup for −10% process wall, '
               '*f*(1 − 1/*s*) = 0.10; "—" means even an infinitely fast stage saves less than 10%. '
               'The ceiling is *f* itself (*s* → ∞).\n')
    out.append('| Target | Workers | symbolic ms | F4 total ms | *f* | *f*<sub>wall</sub> | *s*<sub>10%</sub> by *f* | *s*<sub>10%</sub> by *f*<sub>wall</sub> | ceiling (*f*<sub>wall</sub>) | 2× stage saves |')
    out.append('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for t in TARGETS:
        for w in WORKERS:
            rs = [r for r in cells(stage_records, target=t, workers=w) if ok(r)]
            if not rs:
                continue
            st = [r['report']['statistics'] for r in rs]
            sym = med([s['symbolic_ns'] for s in st])
            tot = med([s['total_ns'] for s in st])
            fs = [s['symbolic_ns'] / s['total_ns'] for s in st]
            f = med(fs)
            plain = [r['process_wall_ns'] for r in cells(wall_records, target=t, workers=w) if ok(r)]
            fw = sym / med(plain) if plain else None
            s10, s10w = needed_speedup(f), (needed_speedup(fw) if fw else None)
            out.append(f'| {t} | {w} | {sym / 1e6:.1f} | {tot / 1e6:.1f} | {f:.3f} [{min(fs):.3f}, {max(fs):.3f}] | '
                       + (f'{fw:.3f}' if fw else '—') + f' | {"%.2f×" % s10 if s10 else "—"} | {"%.2f×" % s10w if s10w else "—"} | '
                       f'−{100 * (fw or f):.1f}% | −{50 * (fw or f):.1f}% |')
    out.append('')


PARTS = ('seed', 'covered', 'divisor', 'shift', 'hash', 'probe_insert', 'residual')


def components(records, out):
    out.append('## Where the serial closure goes (component replay, shipping `Distinct` seeding)\n')
    out.append('Per run, each column sums that part over every batch; the table shows the median over runs '
               'and each part\'s share of the whole closure. `shift`+`hash`+`probe_insert` is the term '
               'stream: shifting every row\'s terms, hashing them, and probing/inserting into the interner '
               '(arena and queue push included). `residual` is the whole closure minus the parts.\n')
    out.append('| Target | runs | batches | closure ms | ' + ' | '.join(PARTS) + ' | queue alone |')
    out.append('|---|---:|---:|---:|' + '---:|' * (len(PARTS) + 1))
    for t in TARGETS:
        rs = [r for r in cells(records, target=t) if ok(r)]
        if not rs:
            continue
        tot = lambda r, k: sum(b[f'{k}_ns'] for b in r['report']['batches'])
        full = med([tot(r, 'full') for r in rs])
        row = [f'{med([tot(r, p) for r in rs]) / 1e6:.1f} ({100 * med([tot(r, p) / tot(r, "full") for r in rs]):.0f}%)'
               for p in PARTS]
        q = med([tot(r, 'queue') for r in rs])
        out.append(f'| {t} | {len(rs)} | {len(rs[0]["report"]["batches"])} | {full / 1e6:.1f} | '
                   + ' | '.join(row) + f' | {q / 1e6:.1f} |')
    out.append('')
    out.append('### Volumes, allocations and memory (first run; counts are deterministic)\n')
    out.append('| Target | rows | columns | terms | terms/column | divisor queries | scan steps/query | '
               'allocations | allocated MiB | peak examined table MiB | peak retained MiB |')
    out.append('|---|' + '---:|' * 10)
    for t in TARGETS:
        rs = [r for r in cells(records, target=t) if ok(r)]
        if not rs:
            continue
        bs = rs[0]['report']['batches']
        s = lambda k: sum(b[k] for b in bs)
        out.append(f"| {t} | {s('rows')} | {s('columns')} | {s('terms')} | {s('terms') / s('columns'):.1f} | "
                   f"{s('divisor_queries')} | {s('divisor_scan_steps') / max(1, s('divisor_queries')):.1f} | "
                   f"{s('allocations')} | {s('allocated_bytes') / 2**20:.0f} | "
                   f"{max(b['examined_table_bytes'] for b in bs) / 2**20:.1f} | "
                   f"{max(b['retained_bytes'] for b in bs) / 2**20:.1f} |")
    out.append('')
    out.append('### Per-batch distribution of the closure (median run)\n')
    out.append('| Target | batches | p50 ms | p90 ms | max ms | share in largest 10% of batches | batches ≥1 ms |')
    out.append('|---|---:|---:|---:|---:|---:|---:|')
    for t in TARGETS:
        rs = [r for r in cells(records, target=t) if ok(r)]
        if not rs:
            continue
        totals = sorted(rs, key=lambda r: sum(b['full_ns'] for b in r['report']['batches']))
        bs = sorted(b['full_ns'] for b in totals[len(totals) // 2]['report']['batches'])
        top = bs[-max(1, len(bs) // 10):]
        out.append(f'| {t} | {len(bs)} | {bs[len(bs) // 2] / 1e6:.2f} | {bs[int(0.9 * (len(bs) - 1))] / 1e6:.2f} | '
                   f'{bs[-1] / 1e6:.1f} | {100 * sum(top) / sum(bs):.0f}% | {sum(1 for b in bs if b >= 1e6)} |')
    out.append('')


def level(records, out):
    out.append('## Level-parallel prototype (#827), replayed on every live batch (`Every` seeding on both sides)\n')
    out.append('Ratio = serial replay / level-parallel replay, formed per run then median [min, max]. '
               '`commit` is the serial in-order commit; `sync` is the dispatched levels\' scan wall minus '
               'their slowest worker slice (spawn, join and imbalance-free waiting); `interned` is the share '
               'of reducer-row terms the commit had to intern itself.\n')
    out.append('| Target | team | runs | serial ms | level-parallel ms | ratio | seed ms | scan ms | commit ms | '
               'sync ms | levels (dispatched) | interned |')
    out.append('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for t in TARGETS:
        for w in WORKERS:
            rs = [r for r in cells(records, target=t, arm=f'level{w}') if ok(r)]
            if not rs:
                continue
            tot = lambda r, k: sum(b[k] for b in r['report']['batches'])
            ratios = [r['report']['replay_serial_ns'] / r['report']['replay_parallel_ns'] for r in rs]
            m = lambda k: med([tot(r, k) for r in rs]) / 1e6
            sync = med([tot(r, 'parallel_scan_ns') - tot(r, 'slowest_slice_ns') for r in rs]) / 1e6
            b0 = rs[0]['report']['batches']
            interned = sum(b['terms_interned'] for b in b0) / max(1, sum(b['terms_interned'] + b['terms_known'] for b in b0))
            out.append(f"| {t} | {w} | {len(rs)} | {med([r['report']['replay_serial_ns'] for r in rs]) / 1e6:.1f} | "
                       f"{med([r['report']['replay_parallel_ns'] for r in rs]) / 1e6:.1f} | "
                       f"{med(ratios):.2f}× [{min(ratios):.2f}, {max(ratios):.2f}] | {m('seed_ns'):.1f} | "
                       f"{m('scan_ns'):.1f} | {m('commit_ns'):.1f} | {sync:.1f} | "
                       f"{sum(b['levels'] for b in b0)} ({sum(b['parallel_levels'] for b in b0)}) | "
                       f"{100 * interned:.0f}% |")
    out.append('')


def ratio_ci(num, den, seed=860):
    """95% bootstrap interval of median(num) / median(den), each arm resampled independently."""
    rng = random.Random(seed)
    rs = sorted(statistics.median(rng.choices(num, k=len(num))) / statistics.median(rng.choices(den, k=len(den)))
                for _ in range(DRAWS))
    return rs[int(0.025 * DRAWS)], rs[int(0.975 * DRAWS) - 1]


INTERN_PHASES = ('spawn', 'seed', 'scan', 'merge', 'emit', 'stitch')


def intern(records, out):
    out.append('## #860 interning prototypes, replayed on every live batch (shipping `Distinct` seeding)\n')
    out.append('Speedup = serial closure / prototype, summed over a run\'s batches, median over runs [min, max]. '
               'Phases are the prototype\'s own clocks (ms, median run). `merge` is the serial walk (serial) or '
               'the three shard phases (sharded); `stitch` is the caller\'s serial assembly between phases. '
               'Shard imbalance is the largest shard\'s candidates over the mean, worst dispatched step.\n')
    out.append('| Target | arm | runs | serial ms | prototype ms | speedup | ' + ' | '.join(INTERN_PHASES)
               + ' | steps (dispatched) | fallback batches | shard imbalance |')
    out.append('|---|---|---:|---:|---:|---:|' + '---:|' * len(INTERN_PHASES) + '---:|---:|---:|')
    for t in TARGETS:
        arms = sorted({r['arm'] for r in records if r['target'] == t}, key=lambda a: (a.rstrip('0123456789'), int(a.lstrip('abcdefghijklmnopqrstuvwxyz'))))
        for arm in arms:
            rs = [r for r in cells(records, target=t, arm=arm) if ok(r)]
            if not rs:
                continue
            sp = [r['report']['replay_serial_ns'] / r['report']['replay_parallel_ns'] for r in rs]
            mid = sorted(rs, key=lambda r: r['report']['replay_parallel_ns'])[len(rs) // 2]
            bs = mid['report']['batches']
            phase = [f"{sum(b[f'{p}_ns'] for b in bs) / 1e6:.1f}" for p in INTERN_PHASES]
            imb = max(b['worst_shard_imbalance_milli'] for b in bs) / 1000
            out.append(f"| {t} | {arm} | {len(rs)} | {med([r['report']['replay_serial_ns'] for r in rs]) / 1e6:.1f} | "
                       f"{med([r['report']['replay_parallel_ns'] for r in rs]) / 1e6:.1f} | "
                       f"{med(sp):.2f}× [{min(sp):.2f}, {max(sp):.2f}] | " + ' | '.join(phase) +
                       f" | {sum(b['steps'] for b in bs)} ({sum(b['dispatched_steps'] for b in bs)}) | "
                       f"{sum(1 for b in bs if b['fallback'])} of {len(bs)} | "
                       + (f'{imb:.2f}' if arm.startswith('sharded') else '—') + ' |')
    out.append('')


def live(records, out):
    out.append('## #860 complete F4 with a prototype serving every batch (process wall, same binary)\n')
    out.append('Ratio = prototype median / shipping (`off`) median at the same worker count, with a 95% '
               'bootstrap interval resampling each arm independently; below 1 is faster. RSS is the peak, '
               'median over runs. Every run\'s basis digest is compared with the shipping arm\'s.\n')
    out.append('| Target | workers | arm | n | wall ms [95% CI] | ratio to off [95% CI] | peak RSS MiB | RSS ratio | basis |')
    out.append('|---|---:|---|---:|---:|---:|---:|---:|---|')
    for t in TARGETS:
        for w in WORKERS:
            base = [r for r in cells(records, target=t, workers=w, arm=f'off{w}') if ok(r)]
            if not base:
                continue
            bw = [r['process_wall_ns'] / 1e6 for r in base]
            brss = med([r['report']['peak_rss_bytes'] / 2**20 for r in base])
            digests = {r['report']['basis_sha256'] for r in base}
            for m in ('off', 'serial', 'sharded'):
                rs = cells(records, target=t, workers=w, arm=f'{m}{w}')
                good = [r for r in rs if ok(r)]
                if not rs:
                    continue
                xs = [r['process_wall_ns'] / 1e6 for r in good]
                lo, hi = ci(xs)
                rss = med([r['report']['peak_rss_bytes'] / 2**20 for r in good])
                same = all(r['report']['basis_sha256'] in digests for r in good) and len(digests) == 1
                if m == 'off':
                    rcell = '—'
                else:
                    rl, rh = ratio_ci(xs, bw)
                    rcell = f'{med(xs) / med(bw):.3f} [{rl:.3f}, {rh:.3f}]'
                fail = len(rs) - len(good)
                out.append(f"| {t} | {w} | {m} | {len(good)}{f' ({fail} failed)' if fail else ''} | "
                           f'{med(xs):.1f} [{lo:.1f}, {hi:.1f}] | {rcell} | {rss:.0f} | {rss / brss:.2f} | '
                           f"{'identical' if same else 'DIFFERS'} |")
    out.append('')


def main():
    d = Path(sys.argv[1])
    out = ['<!-- generated by research/m30-symbolic/summarize.py; do not edit -->\n']
    w, s = jsonl(d / 'walls.jsonl'), jsonl(d / 'stages.jsonl')
    walls(w, out)
    shares(s, w, out)
    components(jsonl(d / 'components.jsonl'), out)
    level(jsonl(d / 'level.jsonl'), out)
    for name, section in (('intern', intern), ('live', live)):
        records = jsonl(d / f'{name}.jsonl')
        if records:
            section(records, out)
    print('\n'.join(out))


if __name__ == '__main__':
    main()
