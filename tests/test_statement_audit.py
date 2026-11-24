"""Regression tests for the independent literal-statement gate."""

import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('statement_audit', ROOT / 'scripts/check-statements.py')
assert spec and spec.loader
statements = importlib.util.module_from_spec(spec)
spec.loader.exec_module(statements)


class StatementGenerationTests(unittest.TestCase):
    def test_actual_publication_proofs_fill_exactly_the_independent_holes(self):
        original = (ROOT / 'Challenge.lean').read_bytes()
        generated = statements.generate_audit_source(original).decode()
        self.assertIn('public import PalomarSolution\n', generated)
        for proof in statements.PROOF_REPLACEMENTS:
            self.assertEqual(generated.count(proof), 1)
        self.assertNotIn('sorry', statements.checks.strip_comments_and_strings(generated))
        for theorem in statements.PROOF_TARGETS:
            name = theorem.rsplit('.', 1)[-1]
            self.assertEqual(statements.checks.theorem_signature(original.decode(), name),
                             statements.checks.theorem_signature(generated, name))
        for name in statements.checks.INTERFACE_NAMES:
            self.assertEqual(statements.checks.public_definition(original.decode(), name),
                             statements.checks.public_definition(generated, name))

    def test_dimension_mutation_is_not_repaired_or_hidden_by_generator(self):
        original = (ROOT / 'Challenge.lean').read_bytes()
        changed = original.replace(b'(hd : 17 < d)', b'(hd : 18 < d)')
        generated = statements.generate_audit_source(changed).decode()
        self.assertIn('(hd : 18 < d)', generated)
        theorem = 'convex_partition_counterexample_gt_17'
        proof = (ROOT / 'AkopyanResearch/Completion/DimensionEighteen.lean').read_text()
        self.assertNotEqual(statements.checks.theorem_signature(generated, theorem),
                            statements.checks.theorem_signature(proof, theorem))

    def test_missing_proof_hole_is_rejected(self):
        original = (ROOT / 'Challenge.lean').read_bytes()
        with self.assertRaisesRegex(ValueError, 'exactly two'):
            statements.generate_audit_source(original.replace(b'  sorry\n', b'  trivial\n', 1))

    def test_ambiguous_namespace_replacement_is_rejected(self):
        original = (ROOT / 'Challenge.lean').read_bytes()
        with self.assertRaisesRegex(ValueError, 'Expected 1 occurrences'):
            statements.generate_audit_source(original + b'namespace AkopyanSixfold\n')


class ProofInputHashTests(unittest.TestCase):
    def fixture(self, root):
        modules = {
            'Challenge': 'public import Mathlib\n',
            'PalomarSolution': 'public import AkopyanResearch.Completion.DimensionEighteen\n',
            'AkopyanResearch.Completion.DimensionEighteen': 'public import Solution Helper.A\n',
            'Solution': 'public import Mathlib\n',
            'Helper.A': 'public import Helper.B\n',
            'Helper.B': 'public import Mathlib\n',
        }
        paths = {}
        for module, source in modules.items():
            path = root / (module.replace('.', '/') + '.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
            paths[module] = path
        for name in ('comparator.json', 'lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
                     'scripts/check-statements.py', 'scripts/check_structure.py',
                     'verification/original-specification/Challenge36.lean.txt',
                     'verification/original-specification/manifest.json'):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('fixture\n')
        return paths

    def test_transitive_proof_sources_are_hashed_and_changes_detected(self):
        with tempfile.TemporaryDirectory(dir=ROOT / 'verification', prefix='statement-regression-') as tmp:
            root = Path(tmp)
            paths = self.fixture(root)
            with mock.patch.object(statements.checks, 'PROJECT_MODULES', paths):
                hashes, modules = statements.proof_input_hashes(root)
            self.assertIn('Helper.B', modules)
            self.assertIn('Helper/B.lean', hashes)
            self.assertIn('Solution.lean', hashes)
            self.assertIn('AkopyanResearch/Completion/DimensionEighteen.lean', hashes)
            self.assertEqual(statements.changed_inputs(root, hashes), [])
            paths['Helper.B'].write_text('public import Mathlib\n-- changed\n')
            self.assertEqual(statements.changed_inputs(root, hashes), ['Helper/B.lean'])
            paths['Helper.A'].unlink()
            self.assertEqual(statements.changed_inputs(root, hashes), ['Helper/A.lean', 'Helper/B.lean'])

    def test_graph_and_hash_use_the_same_source_snapshot(self):
        with tempfile.TemporaryDirectory(dir=ROOT / 'verification', prefix='statement-regression-') as tmp:
            root = Path(tmp)
            paths = self.fixture(root)
            before = paths['Helper.B'].read_bytes()
            original_check = statements.checks.check_imports

            def mutate_after_graph_snapshot(sources):
                paths['Helper.B'].write_text('public import Mathlib\n-- changed during discovery\n')
                return original_check(sources)

            with mock.patch.object(statements.checks, 'PROJECT_MODULES', paths), \
                    mock.patch.object(statements.checks, 'check_imports', mutate_after_graph_snapshot):
                hashes, _ = statements.proof_input_hashes(root)
            self.assertEqual(hashes['Helper/B.lean'], hashlib.sha256(before).hexdigest())
            self.assertEqual(statements.changed_inputs(root, hashes), ['Helper/B.lean'])


if __name__ == '__main__':
    unittest.main()
