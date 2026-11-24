"""Independent numerical checks of the dimension identities used in Solution.lean.

These checks are a regression/sanity test, not a Lean-kernel proof.
The actual universally quantified inequalities are discharged by `omega`
in the Lean theorem `exists_isBlocking_5d`.
"""

import unittest


class DimensionArithmeticTests(unittest.TestCase):
    def test_fivefold_join_of_theorem_a(self):
        # Joining Δ^(n-1)→R^q and Δ^(m-1)→R^r adds vertex counts
        # and produces the target dimension q+r+1.
        vertices, dimension = 36, 6
        for _ in range(4):
            vertices, dimension = vertices + 36, dimension + 6 + 1
        self.assertEqual((vertices, dimension), (180, 34))

    def test_padding_every_dimension_from_36(self):
        for d in range(36, 500):
            k = d - 36
            self.assertEqual(180 + 5 * k, 5 * d)
            self.assertEqual(34 + k, d - 2)

    def test_padding_every_dimension_above_17(self):
        for d in range(18, 500):
            k = d - 18
            self.assertEqual(90 + 5 * k, 5 * d)
            self.assertEqual(16 + k, d - 2)

    def test_rank_four_parameter_bound(self):
        for d in range(18, 500):
            m = 5 * d
            self.assertLess(4 * d + 17 + m * (d - 1), m * d)
        # The strict inequality fails at d = 17; the cutoff matters.
        d, m = 17, 5 * 17
        self.assertEqual(4 * d + 17 + m * (d - 1), m * d)

    def test_rank_five_parameter_bound(self):
        for d in range(18, 500):
            m = 5 * d
            self.assertLess(5 * d - 1 + m * (d - 1), m * d)


if __name__ == '__main__':
    unittest.main()
