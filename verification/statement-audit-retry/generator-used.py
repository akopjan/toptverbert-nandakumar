#!/usr/bin/env python3
"""Kernel-check literal Challenge statements using the actual Solution proofs.

This is an additional statement gate, not the sandboxed Palomar Comparator.
It preserves all interface definitions and theorem statements from Challenge.
Only the enclosing namespace, the two proof holes, and one import are changed.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


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
              'scope': 'Literal independent Challenge statements checked by Lean exact against Solution',
              'full_palomar_workflow': False,
              'comparator_invoked': False,
              'generator_sha256': digest(Path(__file__).read_bytes())}
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    challenge_path = root / 'Challenge.lean'
    solution_path = root / 'Solution.lean'
    original_bytes = challenge_path.read_bytes()
    original = original_bytes.decode('utf-8')
    generated = original
    replacements = [
        ('public import Mathlib\n', 'public import Mathlib\npublic import Solution\n', 1),
        ('namespace AkopyanSixfold\n', 'namespace AkopyanChallengeAudit\n', 1),
        ('end AkopyanSixfold\n', 'end AkopyanChallengeAudit\n', 1),
    ]
    for old, new, expected in replacements:
        if generated.count(old) != expected:
            raise ValueError(f'Expected {expected} occurrences of {old!r}')
        generated = generated.replace(old, new, expected)
    marker = '  sorry\n'
    if generated.count(marker) != 2:
        raise ValueError('Expected exactly two original Challenge proof holes')
    proof_replacements = [
        '  exact AkopyanSixfold.tverberg_counterexample\n',
        '  exact AkopyanSixfold.convex_partition_counterexample d hd\n',
    ]
    for proof in proof_replacements:
        generated = generated.replace(marker, proof, 1)
    reconstructed = generated
    for proof in reversed(proof_replacements):
        if reconstructed.count(proof) != 1:
            raise ValueError('Unexpected generated proof replacement multiplicity')
        reconstructed = reconstructed.replace(proof, marker, 1)
    for old, new, expected in reversed(replacements):
        if reconstructed.count(new) != expected:
            raise ValueError('Unexpected generated namespace/import replacement multiplicity')
        reconstructed = reconstructed.replace(new, old, expected)
    if reconstructed.encode('utf-8') != original_bytes:
        raise ValueError('Generated source differs outside the permitted replacements')
    audit = output / 'StatementAudit.lean'
    audit.write_bytes(generated.encode('utf-8'))
    input_hashes = {
        'Challenge.lean': digest(original_bytes),
        'Solution.lean': digest(solution_path.read_bytes()),
        'lean-toolchain': digest((root / 'lean-toolchain').read_bytes()),
        'lake-manifest.json': digest((root / 'lake-manifest.json').read_bytes()),
        'lakefile.toml': digest((root / 'lakefile.toml').read_bytes()),
    }
    command = ['lake', 'env', 'lean', '-R', str(root), str(audit)]
    start = time.monotonic()
    with (output / 'lean.log').open('wb') as handle:
        process = subprocess.run(command, cwd=root, stdout=handle, stderr=handle)
    changed = [name for name, value in input_hashes.items()
               if digest((root / name).read_bytes()) != value]
    accepted = process.returncode == 0 and not changed
    report.update({
        'outcome': 'literal-statements-accepted' if accepted else 'literal-statement-check-failed',
        'finished_utc': datetime.now(timezone.utc).isoformat(),
        'command': command,
        'lean_exit_code': process.returncode,
        'elapsed_seconds': round(time.monotonic() - start, 3),
        'input_sha256': input_hashes,
        'generated_sha256': digest(audit.read_bytes()),
        'exact_reverse_transformation_matched': True,
        'changed_inputs_during_verification': changed,
        'proof_targets': ['AkopyanSixfold.tverberg_counterexample',
                          'AkopyanSixfold.convex_partition_counterexample'],
        'namespace_replacement': ['AkopyanSixfold', 'AkopyanChallengeAudit'],
        'added_import': 'Solution',
        'proof_replacements': proof_replacements,
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
