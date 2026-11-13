import importlib.util
from pathlib import Path
import unittest
import hashlib
import tempfile
import sys
import os
import subprocess
import time
from unittest import mock

spec = importlib.util.spec_from_file_location('scaling', Path(__file__).parents[1] / 'external/comparand-scaling.py')
scaling = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scaling)


class ComparandScalingTests(unittest.TestCase):
    # Journal payloads retain failed rows once and reject modified committed bytes.
    def test_journal_checkpoint_is_lossless_and_hash_bound(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'cohort.json.gz'
            journal=scaling.AttemptJournal(path,dict(commit='a'*40,attempts=[]))
            row=dict(status='failed',error='missing native answer',stdout='x'*10000,controller_commit='a'*40)
            journal.append(row);journal.stop('interrupted')
            recovered=scaling.load_cohort(path)
            self.assertEqual(recovered['attempts'],[row])
            self.assertEqual(recovered['campaign_stop'],'interrupted')
            recovered['attempts'][0].update(field='13',name='control',engine='fake')
            packed=Path(directory)/'packed.json.gz';scaling.wide.pack(recovered,packed,chunk_size=100)
            self.assertEqual(scaling.wide.load(packed),recovered)
            payload=next((Path(str(path)+'.attempts')).glob('*.gz'))
            payload.write_bytes(b'changed')
            with self.assertRaises(ValueError):scaling.load_cohort(path)
    # A controller-only continuation skips every prior identity and rejects changed instruments.
    def test_resume_reuses_complete_and_refused_cells_without_rerun(self):
        identity=dict(machine='host',physical_cpus=[0,2],cases=[],references={},binaries={},
                      input_exporter={},effective_environment={},rustc='pin',policy=dict(wall=60,workers='1,2',repeats=3,rows='x',fields='13',engines='grobx',diagnostic=False,certify=False,reference_only=False))
        previous=dict(identity,commit='a'*40,attempts=[dict(digest='d',engine='grobx',workers=1,repeat=0,diagnostic=False,status='stopped-by-limit')])
        current=dict(identity,commit='b'*40,attempts=[])
        scaling.check_resume(previous,current)
        self.assertEqual(scaling.attempt_key(previous['attempts'][0]),('d','grobx',1,0,False))
        changed=dict(current,binaries={'grobx':{'sha256':'other'}})
        with self.assertRaises(ValueError):scaling.check_resume(previous,changed)
    # An interrupted uncommitted journal tail is an explicit blocker, never a silently accepted row.
    def test_partial_journal_line_requires_explicit_recovery(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'cohort.json.gz'
            journal=scaling.AttemptJournal(path,dict(commit='a'*40,attempts=[]))
            journal.journal.write_text('{"path":')
            with self.assertRaisesRegex(ValueError,'incomplete journal'):scaling.load_cohort(path)
    # A launcher signal preserves an interrupted attempt after killing and reaping its solver.
    def test_launcher_signal_retains_interruption_boundary(self):
        with tempfile.TemporaryDirectory() as directory,mock.patch.object(scaling.wide.guard,'tree_hwm',side_effect=SystemExit(143)):
            a=scaling.guarded([sys.executable,'-c','import time;time.sleep(30)'],Path(directory)/'run',sorted(os.sched_getaffinity(0))[:1])
            self.assertEqual(a['interrupt_exit'],143)
            self.assertEqual(a['stop'],'launcher-signal-15')
            self.assertNotEqual(a['exit'],0)
    # Native adapter files count toward the output ceiling even when wrapper stdout is tiny.
    def test_adapter_output_is_included_in_storage_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            stem=Path(directory)/'run';adapter=stem.with_suffix('.adapter');adapter.mkdir()
            command=[sys.executable,'-c','from pathlib import Path;Path('+repr(str(adapter/'basis.out'))+').write_text("x"*1000)']
            a=scaling.guarded(command,stem,sorted(os.sched_getaffinity(0))[:1],output_limit=100)
            self.assertTrue(a['stop'].startswith('output-'))
    # Independent Singular references require complete output and exact ordered generator echoes.
    def test_singular_reference_checks_full_echo_and_completion(self):
        case=dict(modulus=13,variables=['x1'],generators=['x1+1'])
        text='@gensize 1\n@gen x1+1\n@gbsize 1\n@gb x1+1\n@lead x1\n@done\n'
        self.assertEqual(scaling.singular_basis(text,case),['x1+1'])
        for bad in [text.replace('@done','missing'),text.replace('@gen x1+1','@gen x1+2')]:
            with self.assertRaises(ValueError):scaling.singular_basis(bad,case)
    # Cancelling a wrapper also kills a detached solver group and lets the wrapper reap it.
    def test_guard_cleans_detached_adapter_solver(self):
        with tempfile.TemporaryDirectory() as directory:
            stem=Path(directory)/'run';leaf=Path(directory)/'leaf';reaped=Path(directory)/'reaped'
            code=('import subprocess,sys,time;from pathlib import Path;'
                  'p=subprocess.Popen([sys.executable,"-c","import time;time.sleep(30)"],start_new_session=True);'
                  'Path('+repr(str(leaf))+').write_text(str(p.pid));p.wait();'
                  'Path('+repr(str(reaped))+').write_text("reaped");time.sleep(30)')
            a=scaling.guarded([sys.executable,'-c',code],stem,sorted(os.sched_getaffinity(0))[:1],wall=.15)
            self.assertIsNotNone(a['stop'])
            self.assertTrue(reaped.exists(),'adapter must reap its separately grouped solver')
            with self.assertRaises(ProcessLookupError):os.kill(int(leaf.read_text()),0)
    # A certified answer with excluded timings supplies only mathematics and never clocks or RSS.
    def test_excluded_certificate_reference_cannot_promote_timings(self):
        case=dict(modulus=13,variables=['x1'],generators=['x1+1'])
        request=dict(case,order='grevlex',workers=1,mode='certified',wall_ns=60*10**9,rss_bytes=2*1024**3)
        raw=dict(input=request,certified=True,flaw=None,stopped=None,cofactors='[[1]]',
                 revision=scaling.wide.REVISIONS['grobx'],isa='x86-64-v3',
                 generator_echoes=['[x1+1]:'],checker_echoes=['[x1+1]:'],
                 input_text='fixture',input_sha256=hashlib.sha256(b'fixture').hexdigest(),basis='[x1+1]:')
        a=dict(status='excluded-environment-overlap',exit=0,stop=None,stdout=__import__('json').dumps(raw),
               process_wall_ns=123,observed_tree_peak_bytes=456)
        ref=scaling.certificate_reference(a,case,60)
        self.assertEqual(ref['basis'],['x1+1'])
        self.assertFalse(ref['timing_eligible'])
        self.assertNotIn('process_wall_ns',ref)
        self.assertNotIn('observed_tree_peak_bytes',ref)
        self.assertEqual(a['status'],'excluded-environment-overlap')
        with self.assertRaises(ValueError):
            scaling.certificate_reference(dict(a,stop='wall-60s'),case,60)
    # Compiler activity refuses a cell before launching any measured solver process.
    def test_compiler_gate_refuses_before_solve(self):
        with tempfile.TemporaryDirectory() as directory,mock.patch.object(scaling,'active_compilers',return_value=[{'pid':1,'command':'rustc'}]):
            a=scaling.execute('msolve',dict(modulus=13,variables=['x1'],generators=['x1']),1,False,
                              {'msolve':{'path':'must-not-run'}},Path(directory)/'run',[0],60)
            self.assertEqual(a['status'],'environment-refused')
            self.assertNotIn('process_wall_ns',a)

    # A compiler seen after a completed process excludes its timing while retaining the attempt.
    def test_compiler_overlap_never_becomes_a_verified_timing(self):
        with tempfile.TemporaryDirectory() as directory,mock.patch.object(scaling,'active_compilers',side_effect=[[],[{'pid':1,'command':'rustc'}]]),mock.patch.object(scaling,'guarded',return_value={'exit':0,'stop':None,'process_wall_ns':123}):
            a=scaling.execute('msolve',dict(modulus=13,variables=['x1'],generators=['x1']),1,False,
                              {'msolve':{'path':'fake'}},Path(directory)/'run',[0],60)
            self.assertEqual(a['status'],'excluded-environment-overlap')
            self.assertEqual(a['process_wall_ns'],123)
    # Offline replay rechecks coefficients instead of trusting a persisted verified status.
    def test_offline_replay_rejects_a_forged_verified_basis(self):
        canonical='characteristic 13\nextension-degree 1\norder grevlex\nvariables x1\ngenerator x1+1\n'
        c=dict(field='13',name='fixture',modulus=13,variables=['x1'],generators=['x1+1'],canonical=canonical,
               digest=hashlib.sha256(canonical.encode()).hexdigest())
        report=dict(commit='a'*40,input_exporter={'sha256':'b'*64},binaries={'msolve':{'sha256':'c'*64}},cases=[c],
                    references={c['digest']:{'basis':['x1+1']}},attempts=[dict(engine='msolve',digest=c['digest'],
                    status='verified',basis=['x1+1'],basis_output='#field characteristic: 13\n#variable order: x1\n#monomial order: graded reverse lexicographical\n#---\n[x1+1]:\n')])
        scaling.validate_cohort(report)
        report['attempts'][0]['basis']=['x1+2']
        with self.assertRaises(ValueError):
            scaling.validate_cohort(report)
    # A zero-exit engine missing its basis keeps all timing and termination evidence as failure.
    def test_missing_basis_keeps_failed_attempt_measurements(self):
        with tempfile.TemporaryDirectory() as directory,mock.patch.object(scaling,'active_compilers',return_value=[]):
            fake=Path(directory)/'fake';fake.write_text('#!/bin/sh\nexit 0\n');fake.chmod(0o755)
            case=dict(modulus=13,variables=['x1'],generators=['x1+1'])
            a=scaling.execute('msolve',case,1,False,{'msolve':{'path':str(fake)}},
                              Path(directory)/'run',sorted(os.sched_getaffinity(0))[:1],60)
            self.assertEqual(a['status'],'failed')
            self.assertEqual(a['exit'],0)
            self.assertIn('process_wall_ns',a)
            self.assertIn('process_cpu_ns',a)
            self.assertIn('observed_tree_peak_bytes',a)

    # Timing children do not inherit the optional diagnostic observer from the caller.
    def test_timing_arm_removes_inherited_observer(self):
        with tempfile.TemporaryDirectory() as directory,mock.patch.dict(os.environ,ZEEBRA_RESEARCH_THREAD_TICKS='1'):
            a=scaling.guarded([sys.executable,'-c','import os; print(os.getenv("ZEEBRA_RESEARCH_THREAD_TICKS"))'],
                              Path(directory)/'run',sorted(os.sched_getaffinity(0))[:1])
            self.assertEqual(a['stdout'].strip(),'None')
    # A successful fast process exceeding the output cap is still retained as a resource stop.
    def test_output_cap_is_enforced_after_exit(self):
        with tempfile.TemporaryDirectory() as directory:
            a=scaling.guarded([sys.executable,'-c','print("x"*1000)'],Path(directory)/'run',
                              sorted(__import__('os').sched_getaffinity(0))[:1],output_limit=100)
            self.assertTrue(a['stop'].startswith('output-'))

    # Reusing an attempt stem cannot read a stale successful msolve basis.
    def test_stale_scratch_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            stem=Path(directory)/'run';stem.with_suffix('.basis').write_text('[x1]:')
            with self.assertRaises(ValueError):
                scaling.execute('msolve',dict(modulus=13),1,False,{},stem,[0],60)
    # Frozen hashes cannot be reused after changing structured generators, field or variable order.
    def test_canonical_identity_binds_structured_input(self):
        canonical='characteristic 13\nextension-degree 1\norder grevlex\nvariables x1\ngenerator x1+1\n'
        case=dict(modulus=13,variables=['x1'],generators=['x1+1'],canonical=canonical,
                  digest=hashlib.sha256(canonical.encode()).hexdigest())
        scaling.canonical_case(case)
        for key,value in [('modulus',17),('variables',['x2']),('generators',['x1+2'])]:
            with self.subTest(key=key),self.assertRaises(ValueError):
                scaling.canonical_case(dict(case,**{key:value}))
    # Pool capacity and idle threads do not count as observed CPU-active workers.
    def test_active_ticks_exclude_idle_capacity(self):
        self.assertEqual(scaling.cpu_activity({'1': 2, '2': 10}, {'1': 6, '2': 10, '3': 1})['active_threads'], 2)

    # Missing or sub-tick hot work is unresolved instead of evidence of serial execution.
    def test_short_hot_region_is_unresolved(self):
        self.assertIsNone(scaling.cpu_activity({'1': 3}, {'1': 3})['active_threads'])

    # A killed or uncertified result never contributes a scaling ratio.
    def test_scaling_requires_verified_completions(self):
        valid = dict(status='verified', process_wall_ns=100)
        self.assertEqual(scaling.speedup(valid, dict(valid, process_wall_ns=50)), 2)
        self.assertIsNone(scaling.speedup(valid, dict(valid, status='stopped-by-limit')))
        self.assertIsNone(scaling.speedup(valid, dict(valid, status='complete')))

    # Pinned serial-only engines keep capability refusals for multiple requested workers.
    def test_serial_engine_refusals_are_explicit(self):
        self.assertIn('serial', scaling.capability('grobx', 2, 32003))
        self.assertIn('serial', scaling.capability('zeebra', 8, 32003))
        self.assertIn('31', scaling.capability('msolve', 1, 18446744073709551263))
        self.assertIsNone(scaling.capability('groebner-rs', 4, 18446744073709551263))

    # Julia uses the installed tasks API and takes thread CPU snapshots around the hot solve.
    def test_julia_script_uses_supported_explicit_policy(self):
        c = dict(variables=['x1'], modulus=13, generators=['x1^2+1'])
        script = scaling.julia_script(c, 8, True)
        self.assertIn('tasks=8', script)
        self.assertIn('linalg=:deterministic', script)
        self.assertNotIn('threaded=', script)
        self.assertLess(script.index('println("@hot_begin'), script.index('zb_G ='))
        self.assertGreater(script.index('println("@hot_end'), script.index('zb_G ='))

    # msolve answers must declare the exact field, ordered variables and complete basis list.
    def test_msolve_ring_and_completion_are_checked(self):
        c = dict(variables=['x1'], modulus=13)
        text = '#field characteristic: 13\n#variable order: x1\n#monomial order: graded reverse lexicographical\n#---\n[x1+1]:\n'
        self.assertEqual(scaling.msolve_basis(text, c), ['x1+1'])
        for bad in [text.replace('13','17'), text.replace('x1\n','x2\n'), text.replace(']:',']')]:
            with self.assertRaises(ValueError):
                scaling.msolve_basis(bad, c)

    # Output verification compares every normalized coefficient rather than ranks or leads.
    def test_changed_basis_tail_is_rejected(self):
        c = dict(variables=['x1'], modulus=13)
        scaling.verify_basis(['2*x1+2'], ['x1+1'], c)
        with self.assertRaises(ValueError):
            scaling.verify_basis(['x1+2'], ['x1+1'], c)


if __name__ == '__main__':
    unittest.main()
