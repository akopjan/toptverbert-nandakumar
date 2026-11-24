"""Unit tests for the source-level checker (no Lean runtime required)."""

import importlib.util
import copy
import hashlib
import json
import subprocess
import sys
import tomllib
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
    def test_omitted_audit_owner_is_detected(self):
        sources = {name: path.read_text() for name, path in checks.PROJECT_MODULES.items()}
        marker = '    `RequestProject.Reduction,'
        self.assertIn(marker, sources['Audit'])
        sources['Audit'] = sources['Audit'].replace(marker, '', 1)
        config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
        with self.assertRaisesRegex(ValueError, 'Audit owner mismatch'):
            checks.check_build_and_audit_coverage(sources, config)

    def test_omitted_private_import_is_detected(self):
        sources = {name: path.read_text() for name, path in checks.PROJECT_MODULES.items()}
        marker = 'import all RequestProject.Reduction\n'
        self.assertIn(marker, sources['Audit'])
        sources['Audit'] = sources['Audit'].replace(marker, '', 1)
        config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
        with self.assertRaisesRegex(ValueError, 'omitted from private imports'):
            checks.check_build_and_audit_coverage(sources, config)

    def test_omitted_public_import_is_detected(self):
        sources = {name: path.read_text() for name, path in checks.PROJECT_MODULES.items()}
        marker = 'public import RequestProject.Reduction\n'
        self.assertIn(marker, sources['Audit'])
        sources['Audit'] = sources['Audit'].replace(marker, '', 1)
        config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
        with self.assertRaisesRegex(ValueError, 'omitted from public imports'):
            checks.check_build_and_audit_coverage(sources, config)

    def test_omitted_build_glob_is_detected(self):
        sources = {name: path.read_text() for name, path in checks.PROJECT_MODULES.items()}
        config = copy.deepcopy(tomllib.loads((ROOT / 'lakefile.toml').read_text()))
        for library in config['lean_lib']:
            if library['name'] == 'RequestProject':
                library['globs'] = []
        with self.assertRaisesRegex(ValueError, 'omitted from Lake build globs'):
            checks.check_build_and_audit_coverage(sources, config)

    def test_comparator_signatures_exact(self):
        challenge = (ROOT / 'Challenge.lean').read_text()
        for full_name, module in checks.PROOF_THEOREMS.items():
            theorem = full_name.rsplit('.', 1)[-1]
            solution = checks.PROJECT_MODULES[module].read_text()
            with self.subTest(theorem=theorem):
                self.assertEqual(checks.theorem_signature(challenge, theorem),
                                 checks.theorem_signature(solution, theorem))

    def test_signature_mismatch_is_detected(self):
        original = (ROOT / 'Challenge.lean').read_text()
        self.assertIn('(hd : 17 < d)', original)
        altered = original.replace('(hd : 17 < d)', '(hd : 18 < d)')
        self.assertNotEqual(checks.theorem_signature(original, 'convex_partition_counterexample_gt_17'),
                            checks.theorem_signature(altered, 'convex_partition_counterexample_gt_17'))

    def test_original_solution_and_specification_are_archived_unchanged(self):
        archive = ROOT / 'verification/original-specification/Challenge36.lean.txt'
        self.assertEqual(hashlib.sha256((ROOT / 'Solution.lean').read_bytes()).hexdigest(),
                         checks.ORIGINAL_SOLUTION_SHA256)
        self.assertEqual(hashlib.sha256(archive.read_bytes()).hexdigest(),
                         checks.ORIGINAL_CHALLENGE36_SHA256)
        old = archive.read_text()
        current = (ROOT / 'Challenge.lean').read_text()
        self.assertEqual(checks.theorem_signature(old, 'tverberg_counterexample'),
                         checks.theorem_signature(current, 'tverberg_counterexample'))
        for name in checks.INTERFACE_NAMES:
            self.assertEqual(checks.public_definition(old, name), checks.public_definition(current, name))

    def test_comparator_uses_publication_entry_point_and_exact_targets(self):
        config = json.loads((ROOT / 'comparator.json').read_text())
        self.assertEqual(config['solution_module'], 'PalomarSolution')
        self.assertEqual(config['theorem_names'], list(checks.PROOF_THEOREMS))
        self.assertEqual(checks.imports((ROOT / 'PalomarSolution.lean').read_text()),
                         {'AkopyanResearch.Completion.DimensionEighteen'})

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

    def test_missing_vendored_module_is_detected(self):
        for prefix in ('Submission', 'Hatcher'):
            with self.subTest(prefix=prefix), self.assertRaisesRegex(ValueError, 'does not exist'):
                checks.check_imports({'Solution': f'public import {prefix}.AbsentModule'})

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
        checks.check_specification_independence(graph)

    def test_multiple_imports_on_one_line_are_all_checked(self):
        self.assertEqual(checks.imports('public import Mathlib Solution Challenge\n'),
                         {'Mathlib', 'Solution', 'Challenge'})
        self.assertEqual(checks.imports('import all Solution\n'), {'Solution'})

    def test_transitive_proof_import_of_specification_is_rejected(self):
        graph = {'Challenge': set(), 'PalomarSolution': {'Bridge'},
                 'Bridge': {'Challenge', 'Solution', 'AkopyanResearch.Completion.DimensionEighteen'},
                 'Solution': set(), 'AkopyanResearch.Completion.DimensionEighteen': {'Solution'}}
        with self.assertRaisesRegex(ValueError, 'depend transitively'):
            checks.check_specification_independence(graph)

    def test_transitive_specification_import_of_proof_is_rejected(self):
        graph = {'Challenge': {'Bridge'}, 'Bridge': {'Solution'}, 'Solution': set(),
                 'PalomarSolution': {'AkopyanResearch.Completion.DimensionEighteen'},
                 'AkopyanResearch.Completion.DimensionEighteen': {'Solution'}}
        with self.assertRaisesRegex(ValueError, 'independent specification'):
            checks.check_specification_independence(graph)

    def test_publication_entry_must_reach_the_new_proof(self):
        graph = {'Challenge': set(), 'PalomarSolution': {'Solution'}, 'Solution': set(),
                 'AkopyanResearch.Completion.DimensionEighteen': {'Solution'}}
        with self.assertRaisesRegex(ValueError, 'actual proof modules'):
            checks.check_specification_independence(graph)

    def test_static_check_cli(self):
        result = subprocess.run([sys.executable, str(ROOT / 'scripts/check_structure.py')],
                                capture_output=True, text=True, cwd=ROOT)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('comparator signatures', result.stdout)


if __name__ == '__main__':
    unittest.main()
