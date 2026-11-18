"""#888: the shipped parallel closure's components, live, via symbolic_cost_model --replay live."""
import json, os, subprocess, sys

binary, output, reps = sys.argv[1], sys.argv[2], int(sys.argv[3])
targets = sys.argv[4].split(',')
workers = [int(w) for w in sys.argv[5].split(',')]
teams = [int(w) for w in sys.argv[6].split(',')] if len(sys.argv) > 6 else None
with open(output, 'a') as out:
    for rep in range(reps):
        for t in (targets if rep % 2 == 0 else targets[::-1]):
            for w, lw in [(w, lw) for w in workers for lw in (teams or [w])][::1 if rep % 2 == 0 else -1]:
                mf = max(512, 48 * lw)
                cmd = [binary, '--target', t, '--workers', str(w), '--replay', 'live', '--merge', 'serial',
                       '--level-workers', str(lw), '--min-frontier', str(mf), '--stages']
                r = subprocess.run(['taskset', '-c', f'8-{7 + w}', *cmd], capture_output=True, text=True, timeout=900)
                rec = dict(rep=rep, target=t, workers=w, team=lw, rc=r.returncode, load1=os.getloadavg()[0])
                if r.returncode == 0:
                    rec['report'] = json.loads(r.stdout)
                else:
                    rec['stderr'] = r.stderr[-800:]
                out.write(json.dumps(rec) + '\n')
                out.flush()
