#!/usr/bin/env python3
import importlib.util
import difflib
import hashlib
import gzip
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('whole_summary',ROOT/'research/m28-current-baseline/summarize.py')
summary=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(summary)


class WholeSummary(unittest.TestCase):
    def source_fixture(self):
        name='examples/profile.rs'
        before='use field::Unused;\nfn main() {}\n'
        after='#[cfg(feature = "research-work")]\nuse field::Unused;\nfn main() {}\n'
        digest=lambda value: hashlib.sha256(value.encode()).hexdigest()
        blob=lambda value: hashlib.sha1(b'blob '+str(len(value.encode())).encode()+b'\0'+value.encode()).hexdigest()
        patch=(f'diff --git a/{name} b/{name}\nindex {blob(before)[:8]}..{blob(after)[:8]} 100644\n'
               +''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+name,tofile='b/'+name)))
        correction=dict(measured_rust_source='a'*40,corrected_file=name,corrected_file_sha256=digest(after))
        snapshot=dict(measured_rust_source='a'*40,files={name:before},corrected_source=after)
        return {name:digest(before)},snapshot,correction,patch

    # Historical source validation reads the retained snapshot rather than the evolving checkout.
    def test_frozen_source_validation_is_independent_of_current_files(self):
        summary.validate_frozen_source(*self.source_fixture())

    # Missing, extra or corrupted frozen files and an unrelated correction fail provenance validation.
    def test_frozen_source_validation_rejects_corruption(self):
        manifest,snapshot,correction,patch=self.source_fixture()
        for files in ({},{**snapshot['files'],'extra.rs':'extra'},{correction['corrected_file']:'corrupt'}):
            with self.subTest(files=files),self.assertRaises(ValueError):
                summary.validate_frozen_source(manifest,dict(snapshot,files=files),correction,patch)
        with self.assertRaises(ValueError):
            summary.validate_frozen_source(manifest,dict(snapshot,corrected_source='different'),correction,patch)
        with self.assertRaises(ValueError):
            summary.validate_frozen_source(manifest,snapshot,correction,patch+'unrelated change\n')

    # Offline replay accepts later checkout edits while still checking the immutable source and correction.
    def test_compilation_provenance_survives_later_source_changes(self):
        manifest,snapshot,correction,source_patch=self.source_fixture()
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            here=root/'research/m28-current-baseline'
            here.mkdir(parents=True)
            for key,name,data in (
                ('source_manifest','manifest.json',json.dumps(manifest).encode()),
                ('frozen_source_snapshot','snapshot.json.gz',gzip.compress(json.dumps(snapshot).encode(),mtime=0)),
                ('patch','correction.patch',source_patch.encode()),
            ):
                path=here/name
                path.write_bytes(data)
                correction['patch_path' if key=='patch' else key]=str(path.relative_to(root))
                correction[key+'_sha256']=hashlib.sha256(data).hexdigest()
            (here/'provenance').mkdir()
            (here/'provenance/post-measurement-import.json').write_text(json.dumps(correction))
            current=root/correction['corrected_file']
            current.parent.mkdir(parents=True)
            current.write_text('later independent source change\n')
            with patch.object(summary,'ROOT',root),patch.object(summary,'HERE',here):
                summary.validate_compilation_correction()

    # A hash-bound outer publication stop permits only the exact durable prefix and missing tail.
    def test_external_publication_stop_is_not_a_solver_refusal(self):
        cells=list(summary.study.plan('native'))
        cohort=dict(phase='native',plan=cells,attempts=[dict(zip(('repeat','problem','modulus','route','arm'),cell)) for cell in cells[:70]])
        ledger=dict(kind='aggregate-watchdog-during-publication',status=124,durable_attempts=70,
                    archive_sha256='archive',unaccepted_cells=[list(c) for c in cells[70:]],
                    prior_controller_charge_seconds=20,window_hard_seconds=880)
        self.assertEqual(summary.external_stop(cohort,ledger,'archive')['reason'],'aggregate-watchdog-during-publication')
        ledger['status']=0
        with self.assertRaises(ValueError): summary.external_stop(cohort,ledger,'archive')
        ledger['status']=124
        ledger['unaccepted_cells']=[]
        with self.assertRaises(ValueError): summary.external_stop(cohort,ledger,'archive')

    # Missing entire cells cannot masquerade as a complete repeated campaign.
    def test_missing_cells_are_rejected(self):
        with self.assertRaises(ValueError): summary.validate_plan(dict(phase='pilot',plan=[],attempts=[]))

    # A stated environmental stop accepts only the exact completed prefix of the frozen plan.
    def test_partial_prefix_requires_refusal(self):
        cells=list(summary.study.plan('pilot'))
        cohort=dict(phase='pilot',plan=cells,attempts=[],refusal=dict(reason='compiler'))
        self.assertFalse(summary.validate_plan(cohort))
        cohort['attempts']=[dict(repeat=1,problem='wrong',modulus=13,route='fglm',arm='stage-on')]
        with self.assertRaises(ValueError): summary.validate_plan(cohort)

    # An eligible-stage ceiling uses the full duration from the same attempt and rejects bad clocks.
    def test_same_attempt_ceiling(self):
        self.assertAlmostEqual(summary.ceiling(100,20),1.25)
        for total,part in [(0,0),(10,11),(10,-1)]:
            with self.assertRaises(ValueError): summary.ceiling(total,part)


if __name__=='__main__': unittest.main()
