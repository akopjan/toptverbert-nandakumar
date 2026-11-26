#!/usr/bin/env python3
"""Kernel-check literal independent Challenge statements against actual proofs.

This is an additional statement gate, not the sandboxed Palomar Comparator.
It preserves every interface definition and both theorem statements from
Challenge. Only the enclosing namespace, two proof holes, and one import
are changed. All transitive local proof sources are hashed before and after
Lean runs; run the project build before this gate to refresh compiled inputs.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

CHECKER_PATH = Path(__file__).resolve().with_name('check_structure.py')
_checker_spec = importlib.util.spec_from_file_location('statement_structure_checks', CHECKER_PATH)
assert _checker_spec and _checker_spec.loader
checks = importlib.util.module_from_spec(_checker_spec)
_checker_spec.loader.exec_module(checks)

PROOF_TARGETS = list(checks.PROOF_THEOREMS)
PROOF_REPLACEMENTS = [
    '  exact AkopyanSixfold.tverberg_counterexample\n',
    '  exact AkopyanSixfold.convex_partition_counterexample_gt_17 d hd\n',
]
SOURCE_REPLACEMENTS = [
    ('public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace\n',
     'public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace\npublic import PalomarSolution\n', 1),
    ('namespace AkopyanSixfold\n', 'namespace AkopyanChallengeAudit\n', 1),
    ('end AkopyanSixfold\n', 'end AkopyanChallengeAudit\n', 1),
]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def generate_audit_source(original_bytes: bytes) -> bytes:
    """Replace only the independently specified holes, namespace, and import."""
    generated = original_bytes.decode('utf-8')
    for old, new, expected in SOURCE_REPLACEMENTS:
        if generated.count(old) != expected:
            raise ValueError(f'Expected {expected} occurrences of {old!r}')
        generated = generated.replace(old, new, expected)
    marker = '  sorry\n'
    if generated.count(marker) != len(PROOF_REPLACEMENTS):
        raise ValueError('Expected exactly two independent Challenge proof holes')
    for proof in PROOF_REPLACEMENTS:
        generated = generated.replace(marker, proof, 1)
    reconstructed = generated
    for proof in reversed(PROOF_REPLACEMENTS):
        if reconstructed.count(proof) != 1:
            raise ValueError('Unexpected generated proof replacement multiplicity')
        reconstructed = reconstructed.replace(proof, marker, 1)
    for old, new, expected in reversed(SOURCE_REPLACEMENTS):
        if reconstructed.count(new) != expected:
            raise ValueError('Unexpected generated namespace/import replacement multiplicity')
        reconstructed = reconstructed.replace(new, old, expected)
    if reconstructed.encode('utf-8') != original_bytes:
        raise ValueError('Generated source differs outside the permitted replacements')
    return generated.encode('utf-8')


def proof_input_hashes(root: Path) -> tuple[dict[str, str], list[str]]:
    """Hash the publication entry point and its complete local proof closure."""
    source_bytes = {name: path.read_bytes() for name, path in checks.PROJECT_MODULES.items()}
    sources = {name: data.decode('utf-8') for name, data in source_bytes.items()}
    graph, _ = checks.check_imports(sources)
    checks.check_specification_independence(graph)
    modules = sorted(checks.dependency_closure(graph, {'PalomarSolution'}))
    paths = {
        'Challenge.lean', 'comparator.json', 'lean-toolchain', 'lake-manifest.json',
        'lakefile.toml', 'scripts/check-statements.py', 'scripts/check_structure.py',
        'verification/original-specification/Challenge36.lean.txt',
        'verification/original-specification/manifest.json',
    }
    hashes = {name: digest((root / name).read_bytes()) for name in sorted(paths)}
    hashes.update({checks.PROJECT_MODULES[module].relative_to(root).as_posix():
                   digest(source_bytes[module]) for module in modules})
    return dict(sorted(hashes.items())), modules


def changed_inputs(root: Path, input_hashes: dict[str, str]) -> list[str]:
    """Report changed or removed inputs, rather than accepting a moving proof."""
    return [name for name, value in input_hashes.items()
            if not (root / name).is_file() or digest((root / name).read_bytes()) != value]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', default='verification/statement-audit')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    output = (root / args.output_dir).resolve()
    if not output.is_relative_to(root / 'verification'):
        parser.error('Statement-audit artifacts must be written under verification/.')
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / 'results.json'
    report = {'outcome': 'verification-in-progress',
              'started_utc': datetime.now(timezone.utc).isoformat(),
              'scope': 'Literal independent Challenge statements checked by Lean exact against PalomarSolution',
              'full_palomar_workflow': False,
              'comparator_invoked': False,
              'generator_sha256': digest(Path(__file__).read_bytes())}
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    input_hashes, proof_modules = proof_input_hashes(root)
    original_bytes = (root / 'Challenge.lean').read_bytes()
    if digest(original_bytes) != input_hashes['Challenge.lean']:
        raise ValueError('Challenge changed while preparing the statement audit')
    audit = output / 'StatementAudit.lean'
    audit.write_bytes(generate_audit_source(original_bytes))
    command = ['lake', 'env', 'lean', '-j1', '-R', str(root), str(audit)]
    start = time.monotonic()
    with (output / 'lean.log').open('wb') as handle:
        process = subprocess.run(command, cwd=root, stdout=handle, stderr=handle)
    changed = changed_inputs(root, input_hashes)
    accepted = process.returncode == 0 and not changed
    report.update({
        'outcome': 'literal-statements-accepted' if accepted else 'literal-statement-check-failed',
        'finished_utc': datetime.now(timezone.utc).isoformat(),
        'command': command,
        'lean_exit_code': process.returncode,
        'elapsed_seconds': round(time.monotonic() - start, 3),
        'input_sha256': input_hashes,
        'proof_input_modules': proof_modules,
        'proof_source_count': len(proof_modules),
        'generated_sha256': digest(audit.read_bytes()),
        'exact_reverse_transformation_matched': True,
        'changed_inputs_during_verification': changed,
        'proof_targets': PROOF_TARGETS,
        'proof_declaration_modules': checks.PROOF_THEOREMS,
        'namespace_replacement': ['AkopyanSixfold', 'AkopyanChallengeAudit'],
        'added_import': 'PalomarSolution',
        'proof_replacements': PROOF_REPLACEMENTS,
    })
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    (output / 'lean.exit').write_text(str(process.returncode) + '\n')
    (output / 'generator-used.py').write_bytes(Path(__file__).read_bytes())
    print(report['outcome'])
    return 0 if accepted else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, UnicodeError) as error:
        print(f'error: {error}', file=sys.stderr)
        sys.exit(1)
