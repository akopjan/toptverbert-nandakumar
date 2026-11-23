"""Unit tests for the source-level checker (no Lean runtime required)."""

import importlib.util
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('check_structure', ROOT / 'scripts/check_structure.py')
assert spec and spec.loader
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)


class CommentLexerTests(unittest.TestCase):
    def test_nested_comments_do_not_produce_admissions(self):
        text = 'theorem t : True := by\n  /- no sorry /- admit -/ axiom -/ exact True.intro\n'
        lexed = checks.strip_comments_and_strings(text)
        self.assertNotIn('sorry', lexed)
        self.assertNotIn('admit', lexed)
        self.assertNotIn('axiom', lexed)
        self.assertIn('exact True.intro', lexed)

    def test_line_comments_and_quoted_strings_are_ignored(self):
        text = 'def x := "sorry -- /- axiom -/"\n-- admit\nexample : True := trivial\n'
        lexed = checks.strip_comments_and_strings(text)
        self.assertNotIn('sorry', lexed)
        self.assertNotIn('admit', lexed)
        self.assertIn('example : True', lexed)

    def test_broken_block_comments_fail(self):
        with self.assertRaises(ValueError):
            checks.strip_comments_and_strings('/- unmatched /- comment -/')

    def test_balanced_delimiters_outside_comments(self):
        checks.check_delimiters('def f := ((3 + [1, 2].length)) /- ) ] } -/')
        with self.assertRaises(ValueError):
            checks.check_delimiters('def f := (3 + 4]')
        with self.assertRaises(ValueError):
            checks.check_delimiters('def f := (3 + 4')

    def test_newline_preservation(self):
        text = 'foo\n/- a\nb -/\n-- comment\nbar'
        self.assertEqual(checks.strip_comments_and_strings(text).count('\n'), text.count('\n'))


class ProjectTests(unittest.TestCase):
    def test_comparator_signatures_exact(self):
        challenge = (ROOT / 'Challenge.lean').read_text()
        solution = (ROOT / 'Solution.lean').read_text()
        for theorem in ('tverberg_counterexample', 'convex_partition_counterexample'):
            with self.subTest(theorem=theorem):
                self.assertEqual(checks.theorem_signature(challenge, theorem),
                                 checks.theorem_signature(solution, theorem))

    def test_signature_mismatch_is_detected(self):
        original = (ROOT / 'Challenge.lean').read_text()
        altered = original.replace('36 ≤ d', '37 ≤ d')
        self.assertNotEqual(checks.theorem_signature(original, 'convex_partition_counterexample'),
                            checks.theorem_signature(altered, 'convex_partition_counterexample'))

    def test_seven_interface_definitions_match(self):
        challenge = (ROOT / 'Challenge.lean').read_text()
        solution = (ROOT / 'Solution.lean').read_text()
        for name in ('simplex', 'DisjointSupports', 'IsAlmostSixEmbedding',
                     'Ambient', 'Body', 'unitBall', 'IsSixPartition'):
            with self.subTest(definition=name):
                self.assertEqual(checks.public_definition(challenge, name),
                                 checks.public_definition(solution, name))

    def test_interface_definition_mismatch_is_detected(self):
        source = (ROOT / 'Challenge.lean').read_text()
        changed = source.replace('∀ v, 0 ≤ x v', '∀ v, 0 < x v')
        self.assertNotEqual(checks.public_definition(source, 'simplex'),
                            checks.public_definition(changed, 'simplex'))

    def test_import_cycle_is_detected(self):
        with self.assertRaisesRegex(ValueError, 'Cyclic import'):
            checks.check_imports({'Challenge': 'public import Solution',
                                  'Solution': 'public import Challenge'})

    def test_missing_project_module_is_detected(self):
        with self.assertRaisesRegex(ValueError, 'does not exist'):
            checks.check_imports({'Solution': 'public import RequestProject.AbsentModule'})

    def test_missing_public_definition_is_detected(self):
        with self.assertRaisesRegex(ValueError, 'Could not locate'):
            checks.public_definition('def other := 42', 'simplex')

    def test_signature_whitespace_is_irrelevant(self):
        first = """theorem target (d : Nat) : 0 ≤ d := by
  exact Nat.zero_le d"""
        second = """theorem target
 (d : Nat)
 : 0 ≤ d := by
  exact Nat.zero_le d"""
        self.assertEqual(checks.theorem_signature(first, 'target'),
                         checks.theorem_signature(second, 'target'))

    def test_graph_has_no_cycles(self):
        sources = {n: path.read_text() for n, path in checks.PROJECT_MODULES.items()}
        graph, count = checks.check_imports(sources)
        self.assertGreater(count, 0)
        self.assertIn('Solution', graph['Audit'])
        self.assertNotIn('Challenge', graph['Solution'])

    def test_static_check_cli(self):
        result = subprocess.run([sys.executable, str(ROOT / 'scripts/check_structure.py')],
                                capture_output=True, text=True, cwd=ROOT)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('comparator signatures', result.stdout)


if __name__ == '__main__':
    unittest.main()
