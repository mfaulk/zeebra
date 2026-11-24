import importlib.util
import unittest
from pathlib import Path

_spec = importlib.util.spec_from_file_location('m34q', Path(__file__).with_name('campaign.py'))
m34q = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(m34q)

REF = 'a' * 64


def rec(status='complete', digest=REF, error=None, route=None, input_digest='d'):
    return dict(status=status, basis_m33=digest, error=error, route=route, digest=input_digest)


class Plan(unittest.TestCase):
    def test_every_arm_runs_at_one_and_at_its_family_maximum(self):
        """Each arm family reaches one worker and its maximum: conventional 1/4/16, signature 1/8/16,
        and the cap, dispatch and #997 arms at 1 and 16."""
        workers = {}
        for arm in m34q.ARMS.values():
            workers.setdefault(arm['family'], set()).update(arm['workers'])
        self.assertEqual(workers['conventional'], {1, 4, 16})
        self.assertEqual(workers['signature'], {1, 8, 16})
        for family in ('cap16', 'adaptive', 'fewest-fl'):
            self.assertEqual(workers[family], {1, 16})

    def test_rows_cover_the_five_fields_and_drop_gf2(self):
        """The plan's rows are the M33-Q correctness rows on the five fields #1011 names, never GF(2)."""
        rows = m34q.rows()
        self.assertEqual({r['field'] for r in rows}, set(m34q.FIELDS))
        self.assertNotIn('gf2', {r['field'] for r in rows})
        self.assertEqual({r['order'] for r in rows}, {'grevlex', 'grlex', 'lex'})

    def test_every_row_has_an_independent_reference(self):
        """Every planned row has an M33-Q reference digest, so no cell is compared against Zeebra."""
        refs = m34q.references()
        for r in m34q.rows():
            self.assertIn(m34q.key(r), refs)
            self.assertNotIn('zeebra', refs[m34q.key(r)]['reference'].lower())

    def test_signature_arms_are_only_expected_to_refuse_off_grevlex(self):
        """Off grevlex the forced signature arms are planned as refusal checks; every other cell expects
        the reference basis."""
        for cell in m34q.plan(m34q.rows()):
            off = cell['row']['order'] != 'grevlex'
            self.assertEqual(cell['expect'] == 'refused', m34q.ARMS[cell['arm']]['family'] == 'signature' and off)


class Verdict(unittest.TestCase):
    def cell(self, arm='P1 conv-w1', order='grevlex'):
        return dict(arm=arm, workers=1, expect='refused' if arm.startswith('P4') and order != 'grevlex'
                    else 'basis', row=dict(order=order, field='m31', name='katsura-8'))

    def test_a_complete_basis_passes_only_on_the_reference_digest(self):
        """A complete attempt passes when its digest equals the reference and fails otherwise."""
        self.assertEqual(m34q.verdict(self.cell(), rec(), REF, 'd'), 'pass')
        self.assertEqual(m34q.verdict(self.cell(), rec(digest='b' * 64), REF, 'd'), 'FAIL digest')

    def test_a_changed_input_is_a_failure_not_a_comparison(self):
        """An input whose digest is not the reference's input is refused before the basis is read."""
        self.assertEqual(m34q.verdict(self.cell(), rec(input_digest='other'), REF, 'd'), 'FAIL input')

    def test_refusals_pass_only_where_the_contract_refuses(self):
        """An Unsupported refusal passes for a signature arm off grevlex and fails anywhere else."""
        refused = rec(status='refused', digest=None, error='Unsupported { .. }')
        self.assertEqual(m34q.verdict(self.cell('P4 sig-w1', 'lex'), refused, REF, 'd'), 'pass (refused)')
        self.assertEqual(m34q.verdict(self.cell(), refused, REF, 'd'), 'FAIL refused')
        self.assertEqual(m34q.verdict(self.cell('P4 sig-w1', 'lex'), rec(), REF, 'd'), 'FAIL not refused')

    def test_a_typed_budget_stop_is_reported_not_passed(self):
        """A typed budget stop is neither a pass nor a correctness failure; it is reported as a stop."""
        stopped = rec(status='stopped', digest=None, error='TimeBudgetExceeded { .. }')
        self.assertEqual(m34q.verdict(self.cell(), stopped, REF, 'd'), 'stopped')

    def test_a_crash_fails(self):
        """A missing or unparseable record is a failure."""
        self.assertEqual(m34q.verdict(self.cell(), None, REF, 'd'), 'FAIL crashed')


if __name__ == '__main__':
    unittest.main()
