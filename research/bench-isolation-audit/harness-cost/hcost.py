"""In-window harness CPU cost of bench-job's run_child (#1104 H-A3).

Usage: hcost.py <repo> <hbusy> <cpus> <out.json> [reps]
The snapshots are stubbed out, so what is measured is only what runs while the child does: the
25 ms frequency sampler, perf stat -p, rss-guard and the taskset/timeout/time wrappers. The harness
is pinned onto the child's CPUs, the no-spare case."""
import json, os, resource, statistics as st, sys, tempfile, time
from pathlib import Path

repo, hbusy, cpus, out = sys.argv[1:5]
reps = int(sys.argv[5]) if len(sys.argv) > 5 else 15
sys.path.insert(0, str(Path(repo) / 'tools'))
import importlib.util
spec = importlib.util.spec_from_file_location('bench_campaign', Path(repo) / 'tools/bench_campaign.py')
campaign = importlib.util.module_from_spec(spec)
spec.loader.exec_module(campaign)

ids = []
for part in cpus.split(','):
    a, _, b = part.partition('-')
    ids += range(int(a), int(b or a) + 1)
os.sched_setaffinity(0, set(ids))

snap_cost = []
for _ in range(5):
    u0 = sum(x.ru_utime + x.ru_stime for x in map(resource.getrusage, (resource.RUSAGE_SELF, resource.RUSAGE_CHILDREN)))
    w0 = time.perf_counter()
    campaign.snapshot(cpus)
    snap_cost.append(dict(cpu=sum(x.ru_utime + x.ru_stime for x in map(resource.getrusage, (resource.RUSAGE_SELF, resource.RUSAGE_CHILDREN))) - u0,
                          wall=time.perf_counter() - w0))
campaign.snapshot = lambda c, start=None: {}

rss = campaign.gnu_time()
perf = campaign.perf_stat()
configs = dict(full=dict(perf=perf, guard=True, rss=rss), sampler_only=dict(perf=None, guard=False, rss=None),
               no_perf=dict(perf=None, guard=True, rss=rss))
results = dict(cpus=cpus, perf=perf, rss_reporter=rss, snapshot=snap_cost, cells=[])
scratch = Path(tempfile.mkdtemp(dir=os.environ.get('TMPDIR')))
for T in (0.24, 1.0, 5.0):
    for name, c in configs.items():
        xs = []
        for _ in range(reps):
            u0 = sum(x.ru_utime + x.ru_stime for x in map(resource.getrusage, (resource.RUSAGE_SELF, resource.RUSAGE_CHILDREN)))
            v0 = resource.getrusage(resource.RUSAGE_SELF).ru_nvcsw
            guard = ('hbusy', hbusy, 64 * 1024 * 1024) if c['guard'] else None
            r = campaign.run_child([hbusy, str(len(ids)), str(T)], cpus, 60, guard=guard, scratch_dir=scratch,
                                   rss_reporter=c['rss'], perf=c['perf'])
            used = sum(x.ru_utime + x.ru_stime for x in map(resource.getrusage, (resource.RUSAGE_SELF, resource.RUSAGE_CHILDREN))) - u0
            xs.append(dict(harness=used - r['cpu_seconds'], child=r['cpu_seconds'], wall=r['process_wall_ns'] / 1e9,
                           self_vcsw=resource.getrusage(resource.RUSAGE_SELF).ru_nvcsw - v0,
                           perf_rc=(r.get('perf') or {}).get('rc'), guard_rc=r.get('rss_guard_rc')))
        h = [x['harness'] for x in xs]
        cell = dict(T=T, config=name, n=reps, harness_median=st.median(h), harness_max=max(h),
                    child_median=st.median(x['child'] for x in xs), wall_median=st.median(x['wall'] for x in xs),
                    vcsw_median=st.median(x['self_vcsw'] for x in xs), perf_rc=sorted({str(x['perf_rc']) for x in xs}),
                    guard_rc=sorted({str(x['guard_rc']) for x in xs}), raw=xs)
        cell['frac_of_capacity'] = cell['harness_median'] / (len(ids) * cell['wall_median'])
        cell['frac_of_child_cpu'] = cell['harness_median'] / cell['child_median']
        results['cells'].append(cell)
        print(f"T={T} {name:13s} harness={cell['harness_median']:.4f}s child={cell['child_median']:.3f}s "
              f"wall={cell['wall_median']:.3f}s of_capacity={cell['frac_of_capacity']:.4%} vcsw={cell['vcsw_median']} "
              f"perf_rc={cell['perf_rc']} guard_rc={cell['guard_rc']}", flush=True)
print('snapshot', [round(s['cpu'], 3) for s in snap_cost], [round(s['wall'], 3) for s in snap_cost])
json.dump(results, open(out, 'w'), indent=1)
