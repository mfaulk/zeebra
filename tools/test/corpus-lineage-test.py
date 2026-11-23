#!/usr/bin/env python3
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('corpus_lineage', ROOT / 'tools/corpus_lineage.py')
lineage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lineage)


def record(name='a', **groups):
    value = dict(schema='corpus-instance-v1', id=name,
                 field=dict(characteristic='13', extension_degree=1, defining_polynomial=[]),
                 variables=['x', 'y'], order='grevlex', task='T-GB',
                 equations=[[dict(exponents=[2, 0], coefficient=['1']),
                             dict(exponents=[0, 2], coefficient=['1'])]],
                 generator=None, source=dict(url='https://example.org/model', revision='v1', license='MIT'),
                 transformations=[],
                 lineage=dict(support_id=name, formulation_id=name, family_id='quadratic',
                              source_id='collection/model', presentation_parent=None,
                              family_parameters=dict(n=2)))
    value['lineage'].update(groups)
    value['normalized_input_digest'] = lineage.input_digest(value)
    return value


def split(protocol='S1', **extra):
    return dict(schema='corpus-split-v1', protocol=protocol,
                assignments=[dict(id='a', partition='development'), dict(id='b', partition='evaluation')], **extra)


def different():
    a, b = record(), record('b')
    b['equations'][0][0]['coefficient'] = ['2']
    b['equations'][0][0]['exponents'] = [1, 0]
    b['normalized_input_digest'] = lineage.input_digest(b)
    return [a, b]


class ManifestTests(unittest.TestCase):
    # Every required identity and provenance field is validated rather than defaulted.
    def test_required_fields(self):
        for key in record():
            with self.subTest(key=key), self.assertRaises(ValueError):
                value = record()
                del value[key]
                lineage.validate_record(value)

    # Unknown fields, malformed digests, duplicate variables and boolean dimensions are rejected.
    def test_bad_shapes(self):
        for key, value in [('surprise', 1), ('task', 'solve'), ('variables', ['x', 'x']),
                           ('normalized_input_digest', 'not-a-digest')]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                r = record()
                r[key] = value
                lineage.validate_record(r)
        r = record()
        r['field']['extension_degree'] = True
        with self.assertRaises(ValueError):
            lineage.validate_record(r)

    # Exponent lengths, coefficient widths, residues and extension definitions must match the field.
    def test_semantic_validation(self):
        for exponents, coefficient in [([1], ['1']), ([1, 0], ['13']), ([1, 0], ['1', '0'])]:
            with self.subTest(exponents=exponents, coefficient=coefficient), self.assertRaises(ValueError):
                r = record()
                r['equations'] = [[dict(exponents=exponents, coefficient=coefficient)]]
                lineage.validate_record(r)
        r = record()
        r['field']['characteristic'] = '1'
        with self.assertRaises(ValueError):
            lineage.validate_record(r)

    # Extension coefficients use a pinned polynomial basis and normalize componentwise.
    def test_extension_field(self):
        r = record()
        r['field'] = dict(characteristic='2', extension_degree=2, defining_polynomial=['1', '1', '1'])
        r['equations'] = [[dict(exponents=[1, 0], coefficient=['1', '1'])]]
        r['normalized_input_digest'] = lineage.input_digest(r)
        lineage.validate_record(r)
        r['field']['defining_polynomial'] = []
        with self.assertRaises(ValueError):
            lineage.validate_record(r)

    # An unsupported schema constraint cannot be silently ignored by the dependency-free validator.
    def test_unknown_schema_keyword(self):
        with self.assertRaisesRegex(ValueError, 'schema keyword'):
            lineage.validate_shape(4, {'type': 'integer', 'maximum': 3})

    # A generated instance pins the revision, call, seed and parameters as well as its exact equations.
    def test_generator_recipe(self):
        r = record()
        r['generator'] = dict(repository='https://example.org/code', revision='a' * 40,
                              path='generator.rs', call=['generate', '--n', '2'], seed=7, parameters=dict(n=2))
        lineage.validate_record(r)
        r['generator']['revision'] = 'main'
        with self.assertRaises(ValueError):
            lineage.validate_record(r)

    # Changing equations without updating the normalized digest invalidates the manifest.
    def test_digest_is_checked(self):
        r = record()
        r['equations'][0][0]['coefficient'] = ['2']
        with self.assertRaisesRegex(ValueError, 'digest'):
            lineage.validate_record(r)

    # Generator and term ordering, repeated terms and zero coefficients normalize identically.
    def test_normalization(self):
        r = record()
        r['equations'].append([dict(exponents=[0, 0], coefficient=['3'])])
        digest = lineage.input_digest(r)
        r['equations'].reverse()
        r['equations'][1].reverse()
        r['equations'][1].extend([dict(exponents=[2, 0], coefficient=['2']),
                                  dict(exponents=[2, 0], coefficient=['11']),
                                  dict(exponents=[1, 0], coefficient=['0'])])
        self.assertEqual(lineage.input_digest(r), digest)

    # Field, ordered variables, order and coefficients remain part of normalized input identity.
    def test_identity_distinctions(self):
        for key, value in [('variables', ['y', 'x']), ('order', 'lex'), ('field', dict(
                characteristic='17', extension_degree=1, defining_polynomial=[]))]:
            with self.subTest(key=key):
                r = record()
                r[key] = value
                self.assertNotEqual(lineage.input_digest(r), record()['normalized_input_digest'])

    # Expanded prime-field text is parsed without making generators monic or accepting unknown syntax.
    def test_legacy_parser(self):
        p = lineage.parse_prime('2*x^2 - x*x + 14*y^2 + 0', 13, ['x', 'y'])
        r = record()
        r['equations'] = [p]
        self.assertEqual(lineage.input_digest(r), record()['normalized_input_digest'])
        for text in ['x/z', '(x+y)^2', 'z', 'x**2', 'x++y', '']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                lineage.parse_prime(text, 13, ['x', 'y'])


class SplitTests(unittest.TestCase):
    # Independent familiar-family records pass S1 while their shared family fails S2.
    def test_family_holdout(self):
        self.assertEqual(lineage.check_split(different(), split()), [])
        self.assertTrue(any('family_id' in e for e in lineage.check_split(different(), split('S2'))))

    # Support and formulation twins cannot cross development/evaluation in S1, S2, S3 or S4.
    def test_related_instances(self):
        for protocol in ['S1', 'S2', 'S3', 'S4']:
            for key in ['support_id', 'formulation_id']:
                with self.subTest(protocol=protocol, key=key):
                    records = different()
                    records[1]['lineage'][key] = 'a'
                    self.assertTrue(any(key in e for e in lineage.check_split(records, split(protocol, **({'scale_parameter': 'n'} if protocol == 'S3' else {})))))

    # Presentation descendants stay with their ancestors even across a chain of transformations.
    def test_transitive_presentation(self):
        records = different() + [record('c', presentation_parent='b')]
        records[1]['lineage']['presentation_parent'] = 'a'
        s = split()
        s['assignments'].append(dict(id='c', partition='evaluation'))
        self.assertTrue(any('presentation' in e for e in lineage.check_split(records, s)))

    # Unresolved parents, cycles, repeated IDs and missing assignments cannot silently pass.
    def test_invalid_catalog_and_assignments(self):
        for mutation in ['parent', 'cycle', 'duplicate', 'missing', 'unknown', 'partition']:
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                records, s = different(), split()
                if mutation == 'parent': records[0]['lineage']['presentation_parent'] = 'missing'
                if mutation == 'cycle':
                    records[0]['lineage']['presentation_parent'] = 'b'
                    records[1]['lineage']['presentation_parent'] = 'a'
                if mutation == 'duplicate': records[1]['id'] = 'a'
                if mutation == 'missing': s['assignments'].pop()
                if mutation == 'unknown': s['assignments'][1]['id'] = 'absent'
                if mutation == 'partition': s['assignments'][1]['partition'] = 'test'
                lineage.check_split(records, s)

    # Equal normalized inputs are flagged even when their declared lineage IDs differ.
    def test_normalized_collision(self):
        self.assertTrue(any('normalized-input' in e for e in lineage.check_split([record(), record('b')], split())))

    # Scale transfer requires an increasing numeric parameter within each evaluated family.
    def test_scale_direction(self):
        records = different()
        records[1]['lineage']['family_parameters']['n'] = 3
        self.assertEqual(lineage.check_split(records, split('S3', scale_parameter='n')), [])
        records[1]['lineage']['family_parameters']['n'] = 1
        self.assertTrue(any('scale' in e for e in lineage.check_split(records, split('S3', scale_parameter='n'))))

    # Field transfer permits support/formulation twins only with disjoint field definitions.
    def test_field_transfer(self):
        records = different()
        records[1]['lineage'].update(support_id='a', formulation_id='a')
        records[1]['field']['characteristic'] = '17'
        records[1]['normalized_input_digest'] = lineage.input_digest(records[1])
        self.assertEqual(lineage.check_split(records, split('S5-field')), [])
        records[1]['field'] = copy.deepcopy(records[0]['field'])
        records[1]['normalized_input_digest'] = lineage.input_digest(records[1])
        self.assertTrue(any('field' in e for e in lineage.check_split(records, split('S5-field'))))

    # Hardware transfer permits the same input on explicitly disjoint hardware contexts.
    def test_hardware_transfer(self):
        r = record()
        s = dict(schema='corpus-split-v1', protocol='S5-hardware', assignments=[
            dict(id='a', partition='development', hardware='host-a'),
            dict(id='a', partition='evaluation', hardware='host-b')])
        self.assertEqual(lineage.check_split([r], s), [])
        s['assignments'][1]['hardware'] = 'host-a'
        with self.assertRaisesRegex(ValueError, 'duplicate assignment'):
            lineage.check_split([r], s)

    # A field-transfer score requires a development formulation twin for every evaluation input.
    def test_field_transfer_requires_matched_formulations(self):
        records = different()
        records[1]['field']['characteristic'] = '17'
        records[1]['normalized_input_digest'] = lineage.input_digest(records[1])
        self.assertTrue(any('formulation twin' in e for e in lineage.check_split(records, split('S5-field'))))

    # Hardware transfer compares the same normalized inputs rather than changing inputs and host together.
    def test_hardware_transfer_requires_matched_inputs(self):
        s = split('S5-hardware')
        s['assignments'][0]['hardware'] = 'host-a'
        s['assignments'][1]['hardware'] = 'host-b'
        self.assertTrue(any('matched inputs' in e for e in lineage.check_split(different(), s)))

    # Equal computed supports cannot evade the split checker through invented support identifiers.
    def test_computed_support(self):
        records = different()
        records[1]['equations'][0][0]['exponents'] = [2, 0]
        records[1]['normalized_input_digest'] = lineage.input_digest(records[1])
        self.assertTrue(any('computed-support' in e for e in lineage.check_split(records, split())))

    # Unknown split protocols and misspelled metadata are rejected rather than weakening checks.
    def test_invalid_protocol(self):
        for s in [split('S6'), split(allow_shared_support=True)]:
            with self.assertRaises(ValueError):
                lineage.check_split(different(), s)


class DrawTests(unittest.TestCase):
    # Hash-ordered whole-group draws are stable when the catalog's row order changes.
    def test_deterministic_group_draw(self):
        records = different() + [record('c', support_id='a')]
        result = lineage.draw_split(records, 'S1', 'test-salt', 1, [])
        self.assertEqual(result, lineage.draw_split(list(reversed(records)), 'S1', 'test-salt', 1, []))
        self.assertEqual(lineage.check_split(records, result), [])
        assignments = {a['id']: a['partition'] for a in result['assignments']}
        self.assertEqual(assignments['a'], assignments['c'])

    # Prior exposure excludes the entire connected lineage group from the untouched draw.
    def test_exposure_closure(self):
        records = different() + [record('c', presentation_parent='a')]
        result = lineage.draw_split(records, 'S1', 'test-salt', 1, ['c'])
        self.assertEqual({a['id'] for a in result['assignments'] if a['partition'] == 'evaluation'}, {'b'})
        with self.assertRaises(ValueError):
            lineage.draw_split(records, 'S1', 'test-salt', 2, ['c'])
        with self.assertRaises(ValueError):
            lineage.draw_split(records, 'S1', 'test-salt', 1, ['missing'])

    # Draw metadata is verified so an edited assignment cannot masquerade as the sealed hash draw.
    def test_draw_tampering(self):
        records = different()
        result = lineage.draw_split(records, 'S1', 'test-salt', 1, [])
        for a in result['assignments']:
            a['partition'] = 'evaluation' if a['partition'] == 'development' else 'development'
        self.assertTrue(any('draw' in e for e in lineage.check_split(records, result)))


class AuditTests(unittest.TestCase):
    # The retained audit is reproducible from tracked inputs without starting any solver.
    def test_retained_audit(self):
        actual = lineage.audit(ROOT)
        expected = json.loads((ROOT / 'research/corpus-lineage/audit.json').read_text())
        self.assertEqual(actual, expected)
        self.assertTrue(actual['unresolved'])
        self.assertTrue(actual['groups']['support_id'])
        self.assertTrue(actual['groups']['formulation_id'])

    # The documented examples validate against both the admission schema and the split checker.
    def test_examples(self):
        records = lineage.load(ROOT / 'research/corpus-lineage/example-catalog.json')
        split_value = lineage.load(ROOT / 'research/corpus-lineage/example-split.json')
        self.assertEqual(lineage.check_split(records, split_value), [])

    # Legacy equation echoes must match their hashed canonical text before normalization is audited.
    def test_legacy_echo_is_bound_to_digest(self):
        case = lineage.load(ROOT / 'research/wide-corpus/cases.json')[0]
        case['generators'][0] = 'x1'
        with self.assertRaisesRegex(ValueError, 'canonical'):
            lineage.legacy_input(case)

    # Historical held-out rows are checked against development by lineage, with unknown supports explicit.
    def test_audit_covers_final_and_historical_splits(self):
        result = lineage.audit(ROOT)
        self.assertEqual(result['counts']['m33_final_reference_entries'], 21)
        final = [r for r in result['rows'] if r['id'].startswith('m33-final/')]
        self.assertEqual(len(final), 21)
        self.assertEqual(sum(r['partition'] == 'evaluation' for r in final), 4)
        self.assertTrue(result['historical_split']['S2_family_crossings'])
        self.assertEqual(result['historical_split']['S1_formulation_crossings'], {})
        self.assertTrue(result['historical_split']['unknown_support_ids'])

    # Known dense and sparse MQ constructions cannot be merged by their similar display names.
    def test_audit_distinguishes_mq_constructions(self):
        result = lineage.audit(ROOT)
        families = {r['family_id'] for r in result['rows']}
        self.assertIn('wide-dense-mq', families)
        self.assertIn('sparse-random-mq', families)
        by_id = {r['id']: r for r in result['rows']}
        self.assertEqual(by_id['m33-final/goldilocks/mq-random-11']['family_id'], 'wide-dense-mq')
        self.assertEqual(by_id['m33-final/m31/mq-random-10']['family_id'], 'sparse-random-mq')
        self.assertTrue(by_id['m33-final/wide64/katsura-9']['normalized_input_digest'])
        qualification = [r for r in result['rows'] if r['id'].startswith('m33-qualification/')]
        self.assertEqual(len(qualification), 71)


    # Duplicate JSON keys and nonfinite numbers fail before manifest validation can hide them.
    def test_strict_json_loading(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / 'bad.json'
            for text in ['{"a":1,"a":2}', '{"a":NaN}', '{"a":Infinity}', '{"a":1e9999}']:
                with self.subTest(text=text), self.assertRaises(ValueError):
                    p.write_text(text)
                    lineage.load(p)

    # Invalid input produces a nonzero CLI status instead of reporting a clean split.
    def test_cli_refuses_bad_input(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / 'bad.json'
            p.write_text('{}')
            result = subprocess.run([sys.executable, str(ROOT / 'tools/corpus_lineage.py'), 'validate', str(p)],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn('error', result.stderr)


class CliTests(unittest.TestCase):
    # The CLI distinguishes clean splits, detected leakage and unreadable metadata by exit status.
    def test_cli_statuses(self):
        with tempfile.TemporaryDirectory() as d:
            catalog, assignment = Path(d) / 'catalog.json', Path(d) / 'split.json'
            assignment.write_text(json.dumps(split()))
            for records, expected in [(different(), 0), ([record(), record('b')], 1), ({}, 2)]:
                with self.subTest(expected=expected):
                    catalog.write_text(json.dumps(records))
                    result = subprocess.run([sys.executable, str(ROOT / 'tools/corpus_lineage.py'),
                                             'check', str(catalog), str(assignment)], capture_output=True)
                    self.assertEqual(result.returncode, expected, result.stderr)


if __name__ == '__main__':
    unittest.main()
