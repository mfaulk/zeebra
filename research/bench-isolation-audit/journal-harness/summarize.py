import json, sys, glob, statistics as st, os


def expand(l):
    out = set()
    for p in l.split(','):
        if '-' in p:
            a, b = map(int, p.split('-'))
            out |= set(range(a, b + 1))
        elif p:
            out.add(int(p))
    return out


rows = []
for jd in glob.glob('/buildcache/bench-jobs/*/'):
    try:
        m = json.load(open(jd + 'manifest.json'))
        f = open(jd + 'journal/journal.jsonl')
    except Exception:
        continue
    runcpus = expand(m['run']['cpus'])
    for line in f:
        try:
            r = json.loads(line)
        except Exception:
            continue
        md = r.get('metadata') or {}
        if r.get('kind') != 'exit' or 'harness_cpu_seconds' not in md or md.get('exit') != 0:
            continue
        cpus = expand(md['cpus'])
        met = (md.get('contamination') or {}).get('metrics') or {}
        rows.append(dict(job=os.path.basename(jd.rstrip('/')), w=r['cell']['workers'], spare=len(runcpus - cpus),
                         h=md['harness_cpu_seconds'], c=md['cpu_seconds'], wall=md['wall_seconds'],
                         foreign=met.get('bench_foreign'), inst=r['cell']['instance'], at=md['after'].get('at')))
print(len(rows), 'attempts from', len({x['job'] for x in rows}), 'jobs')
groups = {}
for x in rows:
    groups.setdefault((x['w'], x['spare'] > 0), []).append(x)
print('w spare n med_harness_s med_attempt_cpu_s med_wall_s med(h/c) frac(h/c<1%) med_foreign p90_foreign')
for (w, sp), xs in sorted(groups.items()):
    hc = [x['h'] / x['c'] for x in xs if x['c'] > 0]
    fo = sorted(x['foreign'] for x in xs if x['foreign'] is not None)
    p90 = fo[int(0.9 * (len(fo) - 1))] if fo else None
    print(w, sp, len(xs), round(st.median(x['h'] for x in xs), 3), round(st.median(x['c'] for x in xs), 3),
          round(st.median(x['wall'] for x in xs), 3), round(st.median(hc), 4) if hc else None,
          round(sum(1 for v in hc if v < 0.01) / len(hc), 3) if hc else None,
          round(st.median(fo), 5) if fo else None, round(p90, 5) if p90 is not None else None)
for sp in (False, True):
    ns = [x for x in rows if x['w'] == 16 and (x['spare'] > 0) == sp and 0.1 <= x['wall'] <= 0.5]
    if ns:
        print(f'16w spare={sp} 0.1-0.5 s walls: n', len(ns), 'med harness', round(st.median(x['h'] for x in ns), 3),
              'med cpu', round(st.median(x['c'] for x in ns), 3), 'med h/c', round(st.median(x['h'] / x['c'] for x in ns), 3),
              'insts', sorted({x['inst'] for x in ns})[:4])
json.dump(rows, open(sys.argv[1], 'w'))
