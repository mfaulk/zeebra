"""Unit tests for the #1165 adapter's pure half: formats, order, canonicalization.

    python3 tools/external/m5gb-paper/test_m5gb_paper.py
"""

import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hash_collision as hc  # noqa: E402
import m5gb_paper as m  # noqa: E402

P = 101
V3 = ["x1", "x2", "x3"]


class Formats(unittest.TestCase):
    def setUp(self):
        m.set_order("grevlex")

    def test_mathic_round_trip(self):
        poly = {(2, 0, 1): 5, (0, 1, 0): 100, (0, 0, 0): 3}
        text = m.format_mathic(poly, 3)
        self.assertEqual(text, "5a2c+100b+3")
        self.assertEqual(m.parse_mathic(text, 3, P), poly)

    def test_mathic_signed_output(self):
        # MathicGB writes coefficients symmetric about zero and drops a unit coefficient.
        self.assertEqual(m.parse_mathic("d2+38ae-33ce-29", 5, P),
                         {(0, 0, 0, 2, 0): 1, (1, 0, 0, 0, 1): 38, (0, 0, 1, 0, 1): 68,
                          (0, 0, 0, 0, 0): 72})

    def test_mathic_upper_case_letters(self):
        n = 30
        e = [0] * n
        e[27] = 2
        self.assertEqual(m.parse_mathic("B2", n, P), {tuple(e): 1})

    def test_zeebra_names_are_matched_whole(self):
        names = [f"x{i}" for i in range(1, 12)]
        poly = m.parse_zeebra("x1*x10 - 2", names, P)
        e = [0] * 11
        e[0] = e[9] = 1
        self.assertEqual(poly, {tuple(e): 1, (0,) * 11: 99})

    def test_zeebra_round_trip(self):
        poly = {(1, 1, 0): 3, (0, 0, 2): 1, (0, 0, 0): 7}
        self.assertEqual(m.parse_zeebra(m.format_zeebra(poly, V3), V3, P), poly)

    def test_grevlex_ties_break_on_the_last_variable(self):
        # x2^2 > x1*x3 under grevlex with x1 > x2 > x3.
        self.assertGreater(m.grevlex_key((0, 2, 0)), m.grevlex_key((1, 0, 1)))
        m.set_order("lex")
        self.assertGreater(m.order_key((1, 0, 1)), m.order_key((0, 2, 0)))

    def test_ideal_header(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "x.ideal")
            m.write_ideal(path, [{(1, 0): 1}, {}], 2, P)
            with open(path) as f:
                self.assertEqual(f.read(), "101 2 1 1 1\n2\na\n0\n")
            m.set_order("lex")
            m.write_ideal(path, [{(1, 0): 1}], 2, P)
            with open(path) as f:
                self.assertEqual(f.readline(), "101 2 lex 0\n")

    def test_gb_file(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "x.gb")
            with open(path, "w") as f:
                f.write("-- gb: ----\n0 ident: <0>  a2-b\n1 a<0>  ab-1\n")
            self.assertEqual(m.parse_gb_file(path, 2, P),
                             [{(2, 0): 1, (0, 1): 100}, {(1, 1): 1, (0, 0): 100}])


class Canonical(unittest.TestCase):
    def setUp(self):
        m.set_order("grevlex")

    def test_minimizes_and_interreduces_a_groebner_basis(self):
        # {x1 - 1, x2 - 2, x1*x2 - 2, 2*x1^2 - 2*x1}: a non-reduced Groebner basis of (x1-1, x2-2).
        basis = [{(1, 0): 1, (0, 0): P - 1}, {(0, 1): 1, (0, 0): P - 2},
                 {(1, 1): 1, (0, 0): P - 2}, {(2, 0): 2, (1, 0): P - 2}]
        reduced, zero, _ = m.canonical_reduced(basis, P)
        self.assertTrue(zero)
        self.assertEqual(reduced, [{(0, 1): 1, (0, 0): P - 2}, {(1, 0): 1, (0, 0): P - 1}])
        self.assertFalse(m.is_reduced(basis, P))
        self.assertTrue(m.is_reduced(reduced, P))

    def test_a_dropped_element_outside_the_minimal_ideal_is_caught(self):
        # x1 and x1^2 + x2: not a Groebner basis of anything that drops x1^2 + x2.
        basis = [{(1, 0): 1}, {(2, 0): 1, (0, 1): 1}]
        _, zero, _ = m.canonical_reduced(basis, P)
        self.assertFalse(zero)

    def test_unit_and_empty(self):
        self.assertEqual(m.canonical_reduced([{(1, 0): 3}, {(0, 0): 5}], P)[0], [{(0, 0): 1}])
        self.assertEqual(m.canonical_reduced([{}], P)[0], [])


class Hash(unittest.TestCase):
    def test_hash_is_linear_so_a_collision_survives_multiplication(self):
        c = hc.hash_coefficients(4)
        a, b, t = (1, 0, 2, 0), (0, 3, 0, 1), (2, 1, 1, 5)
        lhs = (hc.mathic_hash(a, c) - hc.mathic_hash(b, c)) & 0xFFFFFFFF
        ta = tuple(x + y for x, y in zip(a, t))
        tb = tuple(x + y for x, y in zip(b, t))
        self.assertEqual(lhs, (hc.mathic_hash(ta, c) - hc.mathic_hash(tb, c)) & 0xFFFFFFFF)

    def test_monomials_enumerates_every_exponent_vector(self):
        self.assertEqual(len(list(hc.monomials(3, 2))), 10)


if __name__ == "__main__":
    unittest.main()
