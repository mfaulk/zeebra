#!/usr/bin/env python3
"""Bounded worker cohorts using frozen inputs, existing guards and exact reference bases."""
import argparse
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import resource
import shutil
import signal
import statistics
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('wide', Path(__file__).with_name('wide-corpus.py'))
wide = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wide)
WORKERS = (1, 2, 4, 8, 16, 32)


def interrupt(signum, _frame):
    raise SystemExit(128+signum)


def kill_group(process):
    pending=[process.pid];seen=set();groups=set()
    while pending:
        pid=pending.pop()
        if pid in seen:continue
        seen.add(pid)
        try:
            pending.extend(int(p) for p in Path(f'/proc/{pid}/task/{pid}/children').read_text().split())
            groups.add(os.getpgid(pid))
        except (FileNotFoundError,ProcessLookupError):
            pass
    # Adapter supervisors may give their native solver a separate process group.
    # Kill those leaves first while the wrapper can still wait/reap its own children.
    for group in groups & seen - {process.pid,os.getpgrp()}:
        try:os.killpg(group,signal.SIGKILL)
        except ProcessLookupError:pass
    if len(groups)>1:
        until=time.monotonic()+.2
        while time.monotonic()<until and any(Path(f'/proc/{pid}').exists() for pid in seen if pid!=process.pid):
            time.sleep(.005)
    try:
        os.killpg(process.pid,signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def active_compilers():
    result=[]
    names={'cargo','rustc','clippy-driver','cc1','cc1plus','rust-lld','mold'}
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit():continue
        try:
            name=(proc/'comm').read_text().strip()
            status=(proc/'status').read_text()
            if name in names and not re.search(r'^State:\s+Z',status,re.M):
                result.append(dict(pid=int(proc.name),command=(proc/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')[:2048]))
        except (FileNotFoundError,ProcessLookupError,PermissionError):
            pass
    return result


def cpu_activity(before, after):
    deltas = {tid: ticks - before.get(tid, 0) for tid, ticks in after.items()
              if ticks - before.get(tid, 0) > 0}
    return dict(active_threads=len(deltas) if deltas else None, ticks=deltas,
                interpretation='observed lower bound; exited threads and sub-tick work are not counted',
                resolution_hz=os.sysconf('SC_CLK_TCK'))


def capability(engine, workers, modulus):
    if engine in ('zeebra', 'grobx') and workers != 1:
        return 'current production backend is serial'
    if engine == 'msolve' and modulus >= 2**31:
        return 'msolve characteristic must be below 2^31'
    return None


def speedup(one, many):
    if one.get('status') != 'verified' or many.get('status') != 'verified':
        return None
    if min(one.get('process_wall_ns', 0), many.get('process_wall_ns', 0)) <= 0:
        return None
    return one['process_wall_ns'] / many['process_wall_ns']


def verify_basis(basis, reference, case):
    canonical = lambda xs: sorted(wide.canonical_polynomial(p, int(case['modulus']), case['variables']) for p in xs)
    if not basis or canonical(basis) != canonical(reference):
        raise ValueError('complete reduced bases disagree coefficient for coefficient')


def msolve_basis(text, case):
    def header(name):
        match = re.search(r'^#' + re.escape(name) + r':\s*(.*)$', text, re.M)
        if not match:
            raise ValueError('missing msolve ' + name)
        return match[1].strip()
    if (header('field characteristic') != str(case['modulus'])
            or [v.strip() for v in header('variable order').split(',')] != case['variables']
            or header('monomial order') != 'graded reverse lexicographical'):
        raise ValueError('msolve ring differs from requested input')
    start = text.find('[')
    if start < 0:
        raise ValueError('missing basis opening')
    return wide.grobx_work.basis_list(text[start:].strip())


def singular_basis(text,case):
    if not re.search(r'^@done\s*$',text,re.M) or re.search(r'^\s*\?',text,re.M):
        raise ValueError('Singular did not complete')
    echoed=re.findall(r'^@gen (.*)$',text,re.M)
    if len(echoed)!=len(case['generators']):
        raise ValueError('Singular generator count changed')
    for original,actual in zip(case['generators'],echoed):
        verify_basis([actual],[original],case)
    basis=re.findall(r'^@gb (.*)$',text,re.M)
    count=re.search(r'^@gbsize (\d+)$',text,re.M)
    if not count or len(basis)!=int(count[1]):
        raise ValueError('Singular basis is truncated')
    return basis


def julia_script(case, workers, diagnostic=False):
    variables = case['variables']
    # The provisioned 0.10.11 uses tasks and a global threading switch, not threaded=:yes.
    policy = f'ordering=Groebner.DegRevLex(), tasks={workers}, linalg=:deterministic'
    script = ['import Groebner', 'using AbstractAlgebra',
              'Groebner.threading_enabled() || error("threading disabled")',
              'println("@version ", pkgversion(Groebner), " Julia ", VERSION)',
              f'zb_F = AbstractAlgebra.GF({case["modulus"]})',
              f'zb_R, zb_vars = AbstractAlgebra.polynomial_ring(zb_F, {json.dumps(variables)}, internal_ordering=:degrevlex)']
    script += [f'{name} = zb_vars[{i+1}]' for i, name in enumerate(variables)]
    script += ['zb_sys = [' + ', '.join(case['generators']) + ']',
               'for f in zb_sys; println("@gen ", f); end',
               'zb_warm = [zb_vars[1]^2+zb_vars[end]-1,zb_vars[end]^2-zb_vars[1]]',
               f'Groebner.groebner(zb_warm; {policy})', 'GC.gc()']
    if diagnostic:
        script += ['function zb_ticks()', '  result = String[]',
                   '  for tid in readdir("/proc/self/task")',
                   '    try',
                   '      fields = split(split(read("/proc/self/task/"*tid*"/stat",String), ") ",limit=2)[2])',
                   '      push!(result,tid*":"*string(parse(Int,fields[12])+parse(Int,fields[13])))',
                   '    catch; end', '  end', '  join(result,",")', 'end',
                   'zb_ticks()', 'println("@hot_begin ", zb_ticks()); flush(stdout)']
    script += ['zb_start = time_ns()', f'zb_G = Groebner.groebner(zb_sys; {policy})',
               'zb_elapsed = time_ns()-zb_start']
    if diagnostic:
        script += ['println("@hot_end ", zb_ticks())']
    script += ['println("@solve_ns ", zb_elapsed)',
               'println("@workers ", Threads.nthreads())',
               'for g in zb_G; println("@gb ", g); end', 'println("@done 1")']
    return '\n'.join(script) + '\n'


def physical_cpus():
    selected, seen = [], set()
    for cpu in sorted(os.sched_getaffinity(0)):
        topology = Path(f'/sys/devices/system/cpu/cpu{cpu}/topology')
        key = ((topology/'physical_package_id').read_text().strip(), (topology/'core_id').read_text().strip())
        if key not in seen:
            seen.add(key)
            selected.append(cpu)
    return selected


def attempt_output_bytes(stem):
    total=0
    for path in stem.parent.glob(stem.name+'.*'):
        if path.is_file():total+=path.stat().st_size
        elif path.is_dir():
            total+=sum(p.stat().st_size for p in path.rglob('*') if p.is_file())
    return total


def guarded(command, stem, cpus, wall=60, rss=2*1024**3, output_limit=128*1024**2):
    started, peak, stop = time.monotonic_ns(), 0, None
    interrupted=None
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    environment=dict(os.environ, GROEBNER_NO_THREADED='0', OPENBLAS_NUM_THREADS='1', OMP_DYNAMIC='FALSE')
    environment.pop('ZEEBRA_RESEARCH_THREAD_TICKS',None)
    environment['ZEEBRA_AFFINITY']=','.join(map(str,cpus))
    with stem.with_suffix('.stdout').open('w') as out, stem.with_suffix('.stderr').open('w') as err:
        process = subprocess.Popen(['taskset', '-c', ','.join(map(str, cpus)), '/usr/bin/time',
                                   '-o', str(stem.with_suffix('.usage')), '-f', '%U %S %M', *command],
                                   stdout=out, stderr=err, start_new_session=True,
                                   env=environment)
        try:
            while process.poll() is None:
                peak = max(peak, wide.guard.tree_hwm(process.pid))
                output_bytes = attempt_output_bytes(stem)
                if peak > rss or time.monotonic_ns()-started > wall*10**9 or output_bytes > output_limit:
                    stop = 'rss-2GiB' if peak > rss else 'output-128MiB' if output_bytes > output_limit else 'wall-60s'
                    kill_group(process)
                    break
                time.sleep(.005)
        except SystemExit as error:
            interrupted=int(error.code)
            stop='launcher-signal-'+str(interrupted-128)
        except KeyboardInterrupt:
            interrupted=130;stop='launcher-signal-2'
        finally:
            if process.poll() is None:
                kill_group(process)
    finished=time.monotonic_ns()
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    output_bytes=attempt_output_bytes(stem)
    if output_bytes > output_limit:
        stop='output-128MiB'
    if stem.with_suffix('.usage').exists():
        fields = stem.with_suffix('.usage').read_text().splitlines()
        if fields and len(fields[-1].split()) == 3:
            try:
                peak=max(peak,int(fields[-1].split()[2])*1024)
            except ValueError:
                pass
    if peak > rss:
        stop='rss-2GiB-kernel'
    with stem.with_suffix('.stdout').open() as stream:
        stdout=stream.read(output_limit)
    with stem.with_suffix('.stderr').open() as stream:
        stderr=stream.read(output_limit)
    return dict(command=command, cpus=cpus, process_wall_ns=finished-started,
                process_cpu_ns=round((after.ru_utime+after.ru_stime-usage.ru_utime-usage.ru_stime)*1e9),
                observed_tree_peak_bytes=peak, stop=stop, exit=process.returncode,
                interrupt_exit=interrupted,
                output_bytes=output_bytes,
                stdout=stdout,stderr=stderr)


def canonical_case(case):
    if hashlib.sha256(case['canonical'].encode()).hexdigest() != case['digest']:
        raise ValueError('frozen input identity changed')
    lines=case['canonical'].splitlines()
    expected=[f'order grevlex',f'variables {",".join(case["variables"])}']
    if (any(line not in lines for line in expected)
            or [line.removeprefix('generator ') for line in lines if line.startswith('generator ')]!=case['generators']
            or not any(line in lines for line in (f'characteristic {case["modulus"]}',f'prime {case["modulus"]}'))
            or case.get('order','grevlex')!='grevlex'):
        raise ValueError('structured input differs from canonical digest bytes')
    return dict(case, modulus=int(case['modulus']))


def ticks_marker(output, name):
    match = re.search(r'^@'+name+r' (.*)$', output, re.M)
    if not match:
        raise ValueError('missing hot-region snapshot')
    return {tid:int(ticks) for tid,ticks in (part.split(':') for part in match[1].split(',') if part)}


def certified_basis(raw,case,request):
    if (raw.get('input')!=request or raw.get('certified') is not True
            or raw.get('flaw') is not None or raw.get('stopped') is not None or not raw.get('cofactors')
            or raw.get('revision')!=wide.REVISIONS['grobx'] or raw.get('isa')!='x86-64-v3'
            or raw.get('generator_echoes')!=raw.get('checker_echoes')
            or hashlib.sha256(raw.get('input_text','').encode()).hexdigest()!=raw.get('input_sha256')):
        raise ValueError('grobx exact certificate absent or rejected')
    echoes=raw.get('generator_echoes',[])
    if len(echoes)!=len(case['generators']):
        raise ValueError('certified driver changed generator count')
    for original,echo in zip(case['generators'],echoes):
        verify_basis(wide.grobx_work.basis_list(echo),[original],case)
    return wide.grobx_work.basis_list(raw['basis'])


def certificate_reference(attempt,case,wall):
    if (attempt['status'] not in ('verified','excluded-environment-overlap')
            or attempt.get('exit')!=0 or attempt.get('stop')):
        raise ValueError('an incomplete or resource-stopped attempt is not a reference')
    raw=attempt.get('raw') or json.loads(attempt['stdout'])
    request=dict(variables=case['variables'],modulus=int(case['modulus']),order='grevlex',workers=1,
                 generators=case['generators'],mode='certified',wall_ns=wall*10**9,rss_bytes=2*1024**3)
    basis=certified_basis(raw,case,request)
    return dict(basis=basis,timing_eligible=False,source_status=attempt['status'],
                verification='independent exact grobx-checker/cofactors; reference construction timing excluded')


def execute(engine, case, workers, diagnostic, binaries, stem, cpus, wall):
    if any(stem.parent.glob(stem.name+'.*')):
        raise ValueError('attempt scratch already contains outputs')
    refusal = capability(engine, workers, case['modulus'])
    if refusal:
        return dict(status='unsupported', detail=refusal)
    if engine=='zeebra':
        return dict(status='not-measured',detail='current serial whole-route baseline is owned by #751; no parallel shipping route')
    request = dict(variables=case['variables'], modulus=case['modulus'], order='grevlex',
                   generators=case['generators'], workers=workers)
    if engine in ('groebner-rs', 'grobx', 'grobx-certified'):
        native_engine = 'grobx' if engine == 'grobx-certified' else engine
        if engine == 'grobx':
            request.update(mode='raw', wall_ns=wall*10**9, rss_bytes=2*1024**3)
        if engine == 'grobx-certified':
            request.update(mode='certified', wall_ns=wall*10**9,rss_bytes=2*1024**3)
        stem.with_suffix('.request').write_text(json.dumps(request))
        command = [binaries[native_engine]['path'], str(stem.with_suffix('.request'))]
        if diagnostic and engine == 'groebner-rs':
            command=['env','ZEEBRA_RESEARCH_THREAD_TICKS=1',*command]
    elif engine == 'msolve':
        stem.with_suffix('.ms').write_text(','.join(case['variables'])+'\n'+str(case['modulus'])+'\n'+',\n'.join(case['generators'])+'\n')
        command = [binaries[engine]['path'], '-f', str(stem.with_suffix('.ms')), '-o', str(stem.with_suffix('.basis')),
                   '-t',str(workers),'-g','2','-v','2','-l','2']
    elif engine == 'groebner.jl':
        stem.with_suffix('.jl').write_text(julia_script(case, workers, diagnostic))
        command = [binaries[engine]['path'],'--startup-file=no','--history-file=no',f'-t{workers}',
                   '--heap-size-hint=2147483648',str(stem.with_suffix('.jl'))]
    elif engine=='singular':
        adapter=stem.with_suffix('.adapter');adapter.mkdir()
        command=['env','TMPDIR='+str(adapter),binaries[engine]['wrapper'],'--engines','singular',
                 '--retain-artifacts','--measure','--row',case['name'],'--task','reduced-grobner-basis','--characteristic',str(case['modulus']),
                 '--workers','1','--wall',str(wall),'--rss-mib','2048']
    else:
        raise ValueError('unknown engine')
    busy=active_compilers()
    if busy:
        return dict(status='environment-refused',compilers=busy,command=command,cpus=cpus)
    attempt = guarded(command, stem, cpus, wall)
    if engine=='singular':
        attempt['adapter_artifacts']={str(p.relative_to(stem.with_suffix('.adapter'))):p.read_text()[:128*1024**2]
                                      for p in stem.with_suffix('.adapter').rglob('*') if p.is_file()}
    if attempt.get('interrupt_exit'):
        return dict(attempt,status='interrupted')
    busy=active_compilers()
    if busy:
        return dict(attempt,status='excluded-environment-overlap',compilers=busy)
    attempt['status'] = 'stopped-by-limit' if attempt['stop'] else 'failed' if attempt['exit'] else 'complete'
    if attempt['status'] != 'complete':
        return attempt
    try:
        if engine in ('groebner-rs','grobx','grobx-certified'):
            raw = json.loads(attempt['stdout'])
            attempt['raw']=raw
            if engine == 'grobx-certified':
                if raw.get('stopped'):
                    return dict(attempt,raw=raw,status='stopped-by-limit',detail=raw['stopped'])
                basis=certified_basis(raw,case,request)
            else:
                basis = wide.validate_native(raw, request, engine)
            attempt.update(raw=raw, basis=basis, engine_wall_ns=raw.get('solve_ns'))
            if basis is None:
                attempt.update(status='stopped-by-limit', detail=raw['stopped'])
            kernel_peak = raw.get('kernel_peak_rss_bytes') or 0
            attempt['observed_tree_peak_bytes'] = max(attempt['observed_tree_peak_bytes'],kernel_peak)
            if kernel_peak > 2*1024**3:
                attempt.update(status='stopped-by-limit', stop='rss-2GiB-kernel')
            # The existing driver's workers field is pool capacity, never observed participation.
            attempt['concurrency_boundary'] = 'unresolved; driver reports pool capacity only'
            if diagnostic and engine == 'groebner-rs':
                hot=raw['hot_thread_cpu_ticks']
                attempt['hot_activity']=cpu_activity(hot['before'],hot['after'])
                attempt['concurrency_boundary']='hot native F4 call; user+system ticks per OS thread'
        elif engine == 'msolve':
            text = stem.with_suffix('.basis').read_text()
            attempt.update(basis=msolve_basis(text,case), basis_output=text,
                           concurrency_boundary='whole process CPU/wall; no kernel thread-participation claim')
            # Independent native-process CPU exceeding wall proves concurrent CPU use; no JIT here.
            attempt['observed_cpu_parallelism'] = attempt['process_cpu_ns']/attempt['process_wall_ns']
        elif engine=='singular':
            files=attempt['adapter_artifacts']
            row_pattern=r'^-\s+'+re.escape(case['name'])+r'\s+reduced-grobner-basis\s+singular\s+[0-9.]+ ms'
            if not re.search(row_pattern,attempt['stdout'],re.M):
                return dict(attempt,status='stopped-by-limit' if re.search(r'limit|wall|memory',attempt['stdout'],re.I) else 'failed',
                            detail='existing Singular adapter did not admit a complete timing/result')
            reports=[text for text in files.values() if re.search(r'^@gbsize ',text,re.M)]
            if len(reports)!=1:raise ValueError('Singular adapter did not retain one complete answer')
            attempt.update(adapter_artifacts=files,basis=singular_basis(reports[0],case),
                           verification='independent Singular std/redSB through existing adapter')
        else:
            output = attempt['stdout']
            if '@done 1' not in output or 'ERROR:' in output:
                raise ValueError('Julia did not complete')
            echoed = re.findall(r'^@gen (.*)$',output,re.M)
            if len(echoed) != len(case['generators']):
                raise ValueError('Julia generator count changed')
            for original, actual in zip(case['generators'],echoed):
                verify_basis([actual],[original],case)
            if f'@workers {workers}\n' not in output:
                raise ValueError('Julia thread pool differs')
            attempt['basis'] = re.findall(r'^@gb (.*)$', output,re.M)
            attempt['engine_wall_ns'] = int(re.search(r'^@solve_ns (\d+)$',output,re.M)[1])
            if diagnostic:
                attempt['hot_activity'] = cpu_activity(ticks_marker(output,'hot_begin'),ticks_marker(output,'hot_end'))
                attempt['concurrency_boundary'] = 'hot groebner call; user+system CPU ticks per OS thread; may include GC'
    except (ValueError, KeyError, IndexError, OSError) as error:
        attempt.update(status='failed',error=str(error))
    return attempt


def load_cases(binary):
    cases = []
    for modulus in (32003,2147483647):
        for row in ('katsura-4','mq-random-10','katsura-11','cyclic-7','cyclic-10'):
            cases.extend(json.loads(subprocess.check_output([str(binary),'--export-input','--row',row,'--characteristic',str(modulus)],text=True)))
    cases.extend(c for c in json.loads((ROOT/'research/wide-corpus/cases.json').read_text())
                 if c['field'] in ('wide64','goldilocks') and c['name'] in ('katsura-4','mq-random-10','katsura-9','cyclic-7'))
    return [canonical_case(c) for c in cases]


def reference_bases(cases):
    refs = {}
    # #683 references were independently checked by Singular, not just equal across randomized engines.
    for path in (ROOT/'research/competitive/results/grobx-683.json.gz',ROOT/'research/competitive/results/grobx-683-small.json.gz'):
        cohort = wide.load(path)
        for attempt in cohort['attempts']:
            rows = attempt.get('rows',[])
            artifacts = attempt.get('artifacts',{})
            if rows and rows[0]['outcome'] == 'verified' and artifacts.get('basis'):
                refs[artifacts['digest']] = dict(basis=artifacts['basis'], provenance=str(path.relative_to(ROOT)),
                                                verification=rows[0].get('verification'))
    return refs


def validate_cohort(cohort):
    if not re.fullmatch('[0-9a-f]{40}',cohort['commit']):
        raise ValueError('missing exact controller source pin')
    for binary in [cohort['input_exporter'],*cohort['binaries'].values()]:
        if not re.fullmatch('[0-9a-f]{64}',binary['sha256']):
            raise ValueError('missing executable identity')
    cases={c['digest']:canonical_case(c) for c in cohort['cases']}
    for a in cohort['attempts']:
        case=cases[a['digest']]
        if a['status']!='verified':
            continue
        if a.get('stop') or a.get('exit',0):
            raise ValueError('stopped or failed attempt was promoted to verified')
        if a['engine']=='grobx-certified':
            raw=a['raw']
            request=dict(variables=case['variables'],modulus=int(case['modulus']),order='grevlex',
                         workers=1,generators=case['generators'],mode='certified',
                         wall_ns=cohort['policy']['wall']*10**9,rss_bytes=2*1024**3)
            actual=certified_basis(raw,case,request)
        elif a['engine']=='msolve':
            actual=msolve_basis(a['basis_output'],case)
        elif a['engine']=='singular':
            outputs=[t for t in a['adapter_artifacts'].values() if re.search(r'^@gbsize ',t,re.M)]
            if len(outputs)!=1:raise ValueError('Singular reference output absent')
            actual=singular_basis(outputs[0],case)
        elif a['engine'] in ('grobx','groebner-rs'):
            request=dict(variables=case['variables'],modulus=int(case['modulus']),order='grevlex',
                         workers=a['workers'],generators=case['generators'])
            if a['engine']=='grobx':
                request.update(mode='raw',wall_ns=cohort['policy']['wall']*10**9,rss_bytes=2*1024**3)
            actual=wide.validate_native(a['raw'],request,a['engine'])
            version=cohort['binaries'][a['engine']]['version']
            if any(a['raw'].get(k)!=version.get(k) for k in ('revision','build','build_metadata','isa')):
                raise ValueError('native build identity changed inside cohort')
        elif a['engine']=='groebner.jl':
            output=a['stdout']
            if '@done 1' not in output or f'@workers {a["workers"]}\n' not in output:
                raise ValueError('Julia completion or worker setting changed')
            actual=re.findall(r'^@gb (.*)$',output,re.M)
        else:
            raise ValueError('unrecognized verified engine')
        verify_basis(a['basis'],actual,case)
        if a['engine'] not in ('grobx-certified','singular'):
            ref=cohort['references'].get(a['digest'])
            if not ref:
                raise ValueError('verified status lacks an independent exact reference')
            verify_basis(actual,ref['basis'],case)
    return cohort


def warmed_table(cohort):
    groups={}
    for a in cohort['attempts']:
        if a['status']=='verified' and not a['diagnostic'] and a.get('engine_wall_ns',0)>0:
            groups.setdefault((a['digest'],a['engine'],a['workers']),[]).append(a)
    lines=['## Same-engine hot-call curves','','These internal timers exclude process setup/input/output and cannot be divided by another engine’s process wall.',
           'Each S(p) uses this engine/configuration’s own one-worker control; pivot work can change.','',
           '| Field/input | Engine | Workers | Repeats | Hot median [min,max] ms | S(p) | E(p) |','|---|---|---:|---:|---:|---:|---:|']
    for (digest,engine,p),rows in groups.items():
        one=groups.get((digest,engine,1))
        values=[a['engine_wall_ns']/1e6 for a in rows]
        ratio=statistics.median(a['engine_wall_ns'] for a in one)/statistics.median(a['engine_wall_ns'] for a in rows) if one else None
        lines.append('| '+' | '.join([str(rows[0]['field'])+'/'+rows[0]['name'],engine,str(p),str(len(rows)),
            f'{statistics.median(values):.3f} [{min(values):.3f},{max(values):.3f}]',f'{ratio:.3f}' if ratio else '—',f'{ratio/p:.3f}' if ratio else '—'])+' |')
    return '\n'.join(lines)+'\n'


def replay(directory,write=False):
    inventory=json.loads((directory/'inventory.json').read_text())
    boards=['# Comparand scaling cohorts (#739)','','Generated from hash-bound retained attempts; no solver is invoked by replay.',
            'Whole-process, hot-call, certification and diagnostic observations are separate configurations.','']
    count=0
    for filename,digest in inventory['cohorts'].items():
        path=directory/filename
        if hashlib.sha256(path.read_bytes()).hexdigest()!=digest:
            raise ValueError('retained archive identity changed: '+filename)
        cohort=validate_cohort(wide.load(path));count+=len(cohort['attempts'])
        for ref in cohort['references'].values():
            if ref.get('archive_sha256'):
                artifact=directory/Path(ref['provenance']).name
                if hashlib.sha256(artifact.read_bytes()).hexdigest()!=ref['archive_sha256']:
                    raise ValueError('independent reference archive changed')
        boards+=['## '+filename,'']
        with tempfile.TemporaryDirectory() as scratch:
            target=Path(scratch)/'board.md';summarize(cohort,target);boards+=[target.read_text()]
        boards+=[warmed_table(cohort)]
    rendered='\n'.join(boards)
    target=directory/'BOARD.md'
    if write:
        target.write_text(rendered)
    elif target.read_text()!=rendered:
        raise ValueError('generated cohort board is stale')
    print(f'validated {count} retained attempts and regenerated board equality')


def summarize(cohort, target):
    groups = {}
    for a in cohort['attempts']:
        if not a['diagnostic']:
            groups.setdefault((a['digest'],a['engine'],a['workers']),[]).append(a)
    medians = {}
    floors={}
    for key, attempts in groups.items():
        valid = [a for a in attempts if a['status']=='verified']
        if valid:
            medians[key] = dict(status='verified',process_wall_ns=statistics.median(a['process_wall_ns'] for a in valid))
            if valid[0]['name']=='katsura-4':
                floors[(str(valid[0]['field']),key[1],key[2])]=medians[key]['process_wall_ns']
    lines = ['# Comparand worker cohorts (#739)','',f'**Measured at:** `{cohort["commit"]}`.', '',
             'Full reduced-basis process wall; exact reference checks follow timing. Diagnostic hot-region ticks are separate.',
             'Missing verification blocks timing ratios; limits/capabilities remain visible. Julia deterministic backend; Rust randomized native backend.',
             'S(p)/E(p) also require both process walls above twice the corresponding Katsura-4 startup control.', '',
             '| Field/input | Engine | Workers | Repeats | Wall median s | Process CPU median s | RSS max MiB | S(p) | E(p) | Status |',
             '|---|---|---:|---:|---:|---:|---:|---:|---:|---|']
    for (digest,engine,workers),attempts in groups.items():
        first = attempts[0];valid=[a for a in attempts if a['status']=='verified']
        base=medians.get((digest,engine,1)); ours=medians.get((digest,engine,workers))
        ratio=speedup(base,ours) if base and ours else None
        one_floor=floors.get((str(first['field']),engine,1))
        many_floor=floors.get((str(first['field']),engine,workers))
        if (first['name']=='katsura-4' or not one_floor or not many_floor
                or not base or not ours or base['process_wall_ns']<2*one_floor
                or ours['process_wall_ns']<2*many_floor):
            ratio=None
        lines.append('| '+' | '.join([f'{first["field"]}/{first["name"]}',engine,str(workers),str(len(valid)),
            f'{ours["process_wall_ns"]/1e9:.4f} [{min(a["process_wall_ns"] for a in valid)/1e9:.4f},{max(a["process_wall_ns"] for a in valid)/1e9:.4f}]' if ours else '—',
            f'{statistics.median(a["process_cpu_ns"] for a in valid)/1e9:.4f}' if valid else '—',
            f'{max(a["observed_tree_peak_bytes"] for a in valid)/1024**2:.2f}' if valid else '—',
            f'{ratio:.3f}' if ratio else '—', f'{ratio/workers:.3f}' if ratio else '—',
            ', '.join(sorted({a['status'] for a in attempts}))])+' |')
    lines+=['','## Frozen input identities','','| Field/input | Complete canonical SHA-256 |','|---|---|']
    attempted={a['digest'] for a in cohort['attempts']}
    lines += ['| '+str(c['field'])+'/'+c['name']+' | `'+c['digest']+'` |' for c in cohort['cases'] if c['digest'] in attempted]
    target.write_text('\n'.join(lines)+'\n')


def main():
    for signum in (signal.SIGINT,signal.SIGTERM,signal.SIGHUP):
        signal.signal(signum,interrupt)
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary',type=Path)
    parser.add_argument('--input-source',help='exact source commit used to build the input-only exporter')
    parser.add_argument('--oracle-wrapper',type=Path,help='debug competitive_sweep with explicit native-artifact retention')
    parser.add_argument('--oracle-source',help='exact source commit used to build the optional retained oracle wrapper')
    parser.add_argument('--scratch',type=Path)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--replay',type=Path,help='offline coefficient/provenance/board validation of retained campaign directory')
    parser.add_argument('--write-board',action='store_true')
    parser.add_argument('--rows',default='katsura-4,mq-random-10,katsura-11,cyclic-7,cyclic-10,katsura-9')
    parser.add_argument('--engines',default='msolve,groebner.jl,groebner-rs,grobx,zeebra')
    parser.add_argument('--fields',default='32003,2147483647,wide64,goldilocks')
    parser.add_argument('--references',type=Path,nargs='*',default=[],help='previous exact-reference cohort; hashes and full evidence retained')
    parser.add_argument('--reference-only',action='store_true',help='record independent Singular references through existing adapter')
    parser.add_argument('--certify',action='store_true',help='one bounded independent grobx exact/cofactor reference per input')
    parser.add_argument('--workers',default='1,2,4,8,16,32')
    parser.add_argument('--repeats',type=int,default=3)
    parser.add_argument('--wall',type=int,default=60)
    parser.add_argument('--campaign-wall',type=int,default=1200)
    parser.add_argument('--diagnostic',action='store_true')
    parser.add_argument('--summarize',action='store_true')
    args=parser.parse_args()
    if args.replay:
        replay(args.replay,args.write_board);return
    if not args.output:
        parser.error('--output required for measurement/single-cohort summaries')
    if args.summarize:
        summarize(wide.load(args.output),args.output.with_suffix('.md'));return
    if not args.binary or not args.scratch or str(args.scratch.resolve()).startswith(str(Path.home())):
        parser.error('binary and scratch outside home/worktree required')
    if not re.fullmatch('[0-9a-f]{40}',args.input_source or ''):
        parser.error('--input-source requires the exact 40-hex build source commit')
    if args.oracle_wrapper and not re.fullmatch('[0-9a-f]{40}',args.oracle_source or ''):
        parser.error('--oracle-source requires the exact retained-wrapper source commit')
    if args.output.exists():
        parser.error('output exists; use a distinct declared campaign rather than silently pooling')
    if args.scratch.exists():
        parser.error('scratch must be a fresh run-owned directory; stale solver output is refused')
    if not os.environ.get('ZEEBRA_MACHINE'):
        parser.error('set ZEEBRA_MACHINE explicitly')
    if subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True).strip():
        parser.error('commit changes before measurement')
    cpus=physical_cpus()
    workers=[int(p) for p in args.workers.split(',')]
    if not set(workers)<=set(WORKERS) or max(workers)>len(cpus) or args.repeats<1:
        parser.error('invalid worker or repetition grid')
    engines=args.engines.split(',')
    if args.certify:
        engines=['grobx']
        workers=[1]
        args.repeats=1
    binaries={engine:dict(path=shutil.which({'groebner.jl':'julia','groebner-rs':os.environ.get('ZEEBRA_GROEBNER_RS_DRIVER','groebner-rs-driver'),'grobx':'grobx-driver','singular':'Singular'}.get(engine,engine))) for engine in engines if engine!='zeebra'}
    for engine,b in binaries.items():
        if not b['path']:parser.error('unprovisioned '+engine)
        b['sha256']=hashlib.sha256(Path(b['path']).read_bytes()).hexdigest()
        if engine=='singular':
            b['wrapper']=str(args.oracle_wrapper or args.binary)
            b['wrapper_sha256']=hashlib.sha256(Path(b['wrapper']).read_bytes()).hexdigest()
            b['wrapper_source_commit']=args.oracle_source or args.input_source
    cases=load_cases(args.binary);refs=reference_bases(cases)
    for archive in args.references:
        previous=wide.load(archive)
        previous_cases={c['digest']:canonical_case(c) for c in previous['cases']}
        archive_hash=hashlib.sha256(archive.read_bytes()).hexdigest()
        for a in previous['attempts']:
            if a['engine']=='grobx-certified' and a['status'] in ('verified','excluded-environment-overlap'):
                ref=certificate_reference(a,previous_cases[a['digest']],previous['policy']['wall'])
            elif a['engine']=='singular' and a['status']=='verified' and not a.get('stop') and not a.get('exit'):
                outputs=[t for t in a['adapter_artifacts'].values() if re.search(r'^@gbsize ',t,re.M)]
                if len(outputs)!=1:raise ValueError('Singular reference output absent')
                ref=dict(basis=singular_basis(outputs[0],previous_cases[a['digest']]),timing_eligible=False,
                         verification='independent Singular std/redSB through existing adapter')
            else:
                continue
            ref.update(provenance=str(archive),archive_sha256=archive_hash)
            refs[a['digest']]=ref
    started=time.monotonic()
    cohort=dict(schema=1,issue=739,commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        started_at=datetime.now(timezone.utc).isoformat(),machine=os.environ.get('ZEEBRA_MACHINE'),
        cpu=platform.processor(),platform=platform.platform(),physical_cpus=cpus,binaries=binaries,
        rustc=subprocess.check_output(['rustc','-vV'],text=True),policy=vars(args)|{'binary':str(args.binary),'scratch':str(args.scratch),'output':str(args.output)},
        references=refs,cases=cases,attempts=[], input_exporter=dict(path=str(args.binary),sha256=hashlib.sha256(args.binary.read_bytes()).hexdigest(),
            source_commit=args.input_source,build='debug; input-only; outside every timed region'),
        effective_environment=dict(GROEBNER_NO_THREADED='0',OPENBLAS_NUM_THREADS='1',OMP_DYNAMIC='FALSE',
                                   ZEEBRA_RESEARCH_THREAD_TICKS='removed from timing arms; explicitly enabled only in diagnostics'))
    if args.references:
        cohort['policy']['references']=[str(p) for p in args.references]
    cohort['policy']['oracle_wrapper']=str(args.oracle_wrapper) if args.oracle_wrapper else None
    for engine,b in binaries.items():
        if engine in ('groebner-rs','grobx'):
            b['version']=json.loads(subprocess.check_output([b['path'],'--version'],text=True))
        elif engine=='msolve':
            version=subprocess.run([b['path'],'-V'],text=True,capture_output=True,check=True)
            b['version']=version.stdout+version.stderr
    julia_source=Path(os.environ.get('JULIA_DEPOT_PATH',''))/'packages/Groebner/Aqs1M'
    manifest=Path(os.environ.get('JULIA_DEPOT_PATH',''))/'environments/v1.12/Manifest.toml'
    if not manifest.exists():
        manifests=list((Path(os.environ.get('JULIA_DEPOT_PATH',''))/'environments').glob('*/Manifest.toml'))
        manifest=manifests[0] if manifests else None
    if manifest and manifest.exists():
        cohort['julia_manifest']=dict(path=str(manifest),sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),text=manifest.read_text())
    if julia_source.exists():
        cohort['julia_source']={str(p.relative_to(julia_source)):hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in [julia_source/'Project.toml',julia_source/'src/groebner/parameters.jl',julia_source/'src/f4/linalg/linalg.jl']}
    prefix=Path(os.environ.get('ZEEBRA_EXT_PREFIX',str(Path.home()/'.local/opt/zeebra-ext')))
    makefile=prefix/'src/msolve-0.11.0/src/neogb/Makefile'
    if makefile.exists():
        cohort['msolve_build']=dict(path=str(makefile),sha256=hashlib.sha256(makefile.read_bytes()).hexdigest(),
            flags=[line for line in makefile.read_text().splitlines() if re.match(r'^(CC|CFLAGS|SIMD_FLAGS|CPUEXT_FLAGS|OPENMP_CFLAGS|libneogb_la_CFLAGS) =',line)])
    cohort['policy']['references']=[str(p) for p in args.references]
    args.scratch.mkdir(parents=True,exist_ok=True)
    # Worker order alternates between repetitions; timed arms exclude hot snapshot diagnostics.
    stopped={}
    for repeat in range(args.repeats):
        for case in cases:
            if case['name'] not in args.rows.split(',') or str(case['field']) not in args.fields.split(','):continue
            for p in workers if repeat%2==0 else list(reversed(workers)):
                for engine in engines if repeat%2==0 else list(reversed(engines)):
                    if time.monotonic()-started>args.campaign_wall:
                        cohort['campaign_stop']='declared-total-wall';wide.write(args.output,cohort);summarize(cohort,args.output.with_suffix('.md'));return
                    key=(case['digest'],engine)
                    # One serial resource refusal gates the rest of that case/engine grid.
                    gated = key in stopped and (repeat > 0 or p != 16 or args.certify)
                    if gated:
                        a=dict(field=case['field'],name=case['name'],digest=case['digest'],engine=engine,
                               workers=p,repeat=repeat,diagnostic=args.diagnostic,status='skipped-by-gate',
                               detail='serial resource refusal; one 16-worker rescue retained separately')
                        cohort['attempts'].append(a);wide.write(args.output,cohort)
                        continue
                    stem=args.scratch/str(len(cohort['attempts']))
                    actual_engine='grobx-certified' if args.certify else engine
                    try:
                        a=execute(actual_engine,case,p,args.diagnostic,binaries,stem,cpus[:p],args.wall)
                    except (ValueError,KeyError,IndexError) as error:
                        a=dict(status='failed',error=str(error),
                               stdout=stem.with_suffix('.stdout').read_text() if stem.with_suffix('.stdout').exists() else '',
                               stderr=stem.with_suffix('.stderr').read_text() if stem.with_suffix('.stderr').exists() else '')
                    a.update(field=case['field'],name=case['name'],digest=case['digest'],engine=actual_engine,workers=p,repeat=repeat,diagnostic=args.diagnostic)
                    if a['status']=='complete':
                        if args.certify or (args.reference_only and engine=='singular'):
                            a['status']='verified'
                            if args.certify:a['verification']='independent exact grobx-checker/cofactor certificate retained'
                        elif case['digest'] in refs:
                            checking=time.monotonic_ns()
                            try:
                                verify_basis(a['basis'],refs[case['digest']]['basis'],case)
                                a['status']='verified'
                            except ValueError as error:
                                a.update(status='failed',error=str(error))
                            a['verification_wall_ns']=time.monotonic_ns()-checking
                        else:a['verification']='no independent reference retained yet; no ratios'
                    if a['status']=='stopped-by-limit' and p==1:stopped[key]=True
                    elif p==16 and a['status'] in ('complete','verified'):
                        stopped.pop(key,None)
                    cohort['attempts'].append(a);wide.write(args.output,cohort)
                    print(case['field'],case['name'],engine,p,repeat,a['status'],flush=True)
                    if a['status']=='interrupted':
                        cohort['campaign_stop']='launcher-signal';wide.write(args.output,cohort)
                        summarize(cohort,args.output.with_suffix('.md'));raise SystemExit(a['interrupt_exit'])
                    if a['status'] in ('environment-refused','excluded-environment-overlap'):
                        cohort['campaign_stop']='compiler-environment-gate';wide.write(args.output,cohort)
                        summarize(cohort,args.output.with_suffix('.md'));raise SystemExit(75)
                    if a['status']=='failed':raise RuntimeError('unexpected engine failure retained')
    cohort['elapsed_seconds']=time.monotonic()-started
    wide.write(args.output,cohort);summarize(cohort,args.output.with_suffix('.md'))


if __name__=='__main__':
    main()
