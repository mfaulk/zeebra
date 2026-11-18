"""#890: interleaved per-commit one-worker runs. Builds rotate per rep; one JSON line per child."""
import argparse, json, os, subprocess, time

p = argparse.ArgumentParser()
p.add_argument('--bindir', required=True)
p.add_argument('--builds', required=True)
p.add_argument('--target', required=True)
p.add_argument('--reps', type=int, default=5)
p.add_argument('--output', required=True)
p.add_argument('--extra', default='--stages')
p.add_argument('--first-rep', type=int, default=0)
a = p.parse_args()
builds = a.builds.split(',')
cpus = open('/proc/self/status').read().split('Cpus_allowed_list:')[1].split()[0]
with open(a.output, 'a') as out:
    for rep in range(a.first_rep, a.first_rep + a.reps):
        k = rep % len(builds)
        order = builds[k:] + builds[:k]
        if rep % 2:
            order.reverse()
        for b in order:
            load = os.getloadavg()[0]
            t0 = time.perf_counter_ns()
            r = subprocess.run([os.path.join(a.bindir, b), '--target', a.target, '--workers', '1',
                                *a.extra.split()], capture_output=True, text=True, timeout=600)
            wall = time.perf_counter_ns() - t0
            rec = dict(rep=rep, build=b, target=a.target, cpus=cpus, load1=load, process_wall_ns=wall,
                       rc=r.returncode, stderr=r.stderr[-500:] if r.returncode else '')
            if r.returncode == 0:
                rep_json = json.loads(r.stdout)
                s = rep_json['statistics']
                rec.update(basis_sha256=rep_json.get('basis_sha256'), peak_rss_bytes=rep_json.get('peak_rss_bytes'),
                           f4_call_ns=rep_json.get('f4_call_ns'),
                           stats={k: v for k, v in s.items() if not isinstance(v, (dict, list))})
            out.write(json.dumps(rec) + '\n')
            out.flush()
