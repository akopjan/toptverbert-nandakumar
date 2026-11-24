#!/usr/bin/env python3
"""Read-only publication preflight; does not run Lean or certify a theorem.

Scan all submitted source paths, not just Lake roots.  Evidence is a dated
working-tree snapshot; rerun after the final proof and audit integration.
"""
from __future__ import annotations

import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import tomllib

import yaml

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
EXCLUDED = {'.git', '.lake'}
COMPILED = {'.a', '.bc', '.dll', '.dylib', '.ilean', '.ir', '.o', '.obj',
            '.olean', '.so', '.trace'}
COMPILED_NAME_SUFFIXES = ('.olean.private', '.olean.server', '.ir.sig')
ALLOWED_AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def module_header(source: str) -> bool:
    """Lexical header check, with nested ordinary comments and line comments."""
    i = 0
    while i < len(source):
        if source[i].isspace():
            i += 1
        elif source.startswith('--', i):
            i = source.find('\n', i)
            if i < 0:
                return False
        elif source.startswith('/-', i):
            if source.startswith('/-!', i) or source.startswith('/--', i):
                return False
            level = 1
            i += 2
            while i < len(source) and level:
                if source.startswith('/-', i):
                    level += 1
                    i += 2
                elif source.startswith('-/', i):
                    level -= 1
                    i += 2
                else:
                    i += 1
            if level:
                return False
        else:
            return re.match(r'module\b', source[i:]) is not None
    return False


def main() -> None:
    spec = importlib.util.spec_from_file_location('project_structure', ROOT / 'scripts/check_structure.py')
    assert spec is not None and spec.loader is not None
    structure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(structure)
    snapshot = []
    violations = []
    artifacts = []
    lfs = []
    for dirname, dirs, filenames in os.walk(ROOT, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in EXCLUDED)
        for filename in sorted(filenames):
            path = Path(dirname) / filename
            rel = str(path.relative_to(ROOT))
            if (path.suffix.lower() in COMPILED
                    or path.name.lower().endswith(COMPILED_NAME_SUFFIXES)):
                artifacts.append(rel)
            if not path.is_symlink() and path.is_file():
                with path.open('rb') as stream:
                    if stream.read(80).startswith(b'version https://git-lfs.github.com/spec/v1'):
                        lfs.append(rel)
            if path.suffix != '.lean':
                continue
            if path.is_symlink():
                violations.append({'path': rel, 'reason': 'Lean symbolic link'})
                continue
            data = path.read_bytes()
            source = data.decode('utf-8')
            lines = data.count(b'\n') + bool(data and not data.endswith(b'\n'))
            header = filename == 'lakefile.lean' or module_header(source)
            lexical = structure.strip_comments_and_strings(source)
            admissions = {word: len(re.findall(r'\b' + word + r'\b', lexical))
                          for word in ('sorry', 'admit', 'axiom')}
            snapshot.append({'path': rel, 'sha256': sha(data), 'bytes': len(data),
                             'physical_lines': lines, 'module_header_lexical': header,
                             'admission_tokens': admissions})
            if not header:
                violations.append({'path': rel, 'reason': 'missing module header or preceding documentation comment'})
            if lines > 10000:
                violations.append({'path': rel, 'reason': 'more than 10000 physical lines', 'lines': lines})
    snapshot.sort(key=lambda row: row['path'])
    challenge = next(row for row in snapshot if row['path'] == 'Challenge.lean')
    config_bytes = (ROOT / 'comparator.json').read_bytes()
    config = json.loads(config_bytes)
    config_keys = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}
    config_ok = (config_keys <= config.keys()
                 and config.keys() <= config_keys | {'definition_names', 'enable_nanoda'}
                 and config['challenge_module'] == 'Challenge'
                 and config['solution_module'] == 'PalomarSolution'
                 and config['theorem_names'] == list(structure.PROOF_THEOREMS)
                 and set(config['permitted_axioms']) == ALLOWED_AXIOMS
                 and len(config_bytes) <= 1024 * 1024)
    graph = {}
    missing_imports = []
    for name, path in structure.PROJECT_MODULES.items():
        imported = structure.imports(path.read_text())
        graph[name] = imported & structure.PROJECT_MODULES.keys()
        for dep in imported:
            if dep not in structure.PROJECT_MODULES and any(
                    dep == prefix or dep.startswith(prefix + '.') for prefix in structure.PROJECT_PREFIXES):
                missing_imports.append({'source': name, 'import': dep})
    try:
        structure.check_specification_independence(graph)
        independence = {'result': 'pass', 'method': 'transitive local source import graph'}
    except ValueError as error:
        independence = {'result': 'fail', 'reason': str(error)}
    signatures = {}
    challenge_source = (ROOT / 'Challenge.lean').read_text()
    for theorem, owner in structure.PROOF_THEOREMS.items():
        leaf = theorem.rsplit('.', 1)[1]
        signatures[theorem] = (
            structure.theorem_signature(challenge_source, leaf)
            == structure.theorem_signature(structure.PROJECT_MODULES[owner].read_text(), leaf))
    interfaces = {name: structure.public_definition(challenge_source, name)
                       == structure.public_definition((ROOT / 'Solution.lean').read_text(), name)
                  for name in structure.INTERFACE_NAMES}
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    packages = manifest['packages']
    pins_ok = all(p['type'] == 'git' and re.fullmatch('[0-9a-f]{40}', p['rev'])
                  and re.fullmatch(r'https://github\.com/[^/?#\s]+/[^/?#\s]+', p['url'])
                  for p in packages)
    mathlib = next(p for p in packages if p['name'] == 'mathlib')
    toolchain = (ROOT / 'lean-toolchain').read_text().strip()
    mathlib_toolchain_path = ROOT / '.lake/packages/mathlib/lean-toolchain'
    mathlib_toolchain = mathlib_toolchain_path.read_text().strip()
    workflow = yaml.safe_load((ROOT / '.github/workflows/verify.yml').read_text())
    steps = workflow['jobs']['verify']['steps']
    actions = [s['uses'] for s in steps if 'uses' in s]
    lean_step = next(s for s in steps if s.get('uses', '').startswith('leanprover/lean-action@'))
    lean_action = yaml.safe_load((HERE / 'official-references/lean-action-action.yml').read_text())
    lake = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    license_pattern = re.compile(r'(LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(\.(md|markdown|txt))?', re.I)
    license_files = [p.name for p in ROOT.iterdir() if license_pattern.fullmatch(p.name)]
    config_files = ['Challenge.lean', 'PalomarSolution.lean', 'comparator.json', 'lakefile.toml',
                    'lean-toolchain', 'lake-manifest.json', '.github/workflows/verify.yml',
                    'scripts/verify.sh', 'scripts/verify-comparator.sh',
                    'scripts/check_structure.py', 'scripts/check-statements.py']
    proof_rows = [r for r in snapshot if r['path'] != 'Challenge.lean'
                  and not {'verification', 'tests'}.intersection(Path(r['path']).parts[:-1])]
    report = {
        'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope': ('Working-tree static source and configuration snapshot only. '
                  'This script does not run or determine the status of builds, '
                  'owner audits, independent kernels, Comparator, CI or registry '
                  'acceptance. Read their separately recorded evidence.'),
        'source_scan': {'regular_lean_files': len(snapshot), 'exclusions': sorted(EXCLUDED),
                        'violations': violations, 'longest': max(snapshot, key=lambda r: r['physical_lines']),
                        'compiled_artifacts_outside_lake': artifacts, 'lfs_pointers': lfs,
                        'gitmodules_present': (ROOT / '.gitmodules').exists()},
        'challenge': {'physical_lines': challenge['physical_lines'], 'bytes': challenge['bytes'],
                      'hard_limits_pass': challenge['physical_lines'] <= 1000 and challenge['bytes'] <= 100 * 1024,
                      'recommended_limits_pass': challenge['physical_lines'] <= 300 and challenge['bytes'] <= 32 * 1024,
                      'imports': sorted(structure.imports(challenge_source)),
                      'intentional_sorry_tokens': challenge['admission_tokens']['sorry'],
                      'independence': independence, 'signatures_match_actual_owners': signatures,
                      'seven_interface_definitions_match_original': interfaces},
        'comparator': {'configuration_pass': config_ok, 'configuration': config,
                       'execution': 'not executed or assessed by this static script',
                       'separate_evidence': 'verification/d18-comparator/results.json'},
        'lexical_proof_scan': {'files': len(proof_rows),
                              'counts': {word: sum(r['admission_tokens'][word] for r in proof_rows)
                                         for word in ('sorry', 'admit', 'axiom')},
                              'qualification': 'Token scan is not a dependency axiom audit.'},
        'source_import_graph': {'missing_local_imports': missing_imports,
                               'publication_closure_size': len(structure.dependency_closure(graph, {'PalomarSolution'}))},
        'dependencies': {'lean_toolchain': toolchain, 'mathlib_toolchain': mathlib_toolchain,
                         'toolchains_match': toolchain == mathlib_toolchain,
                         'official_minimum': json.loads((HERE / 'official-references/PalomarSubmission-toolchains.json').read_text())['minimum'],
                         'pins_valid_shape': bool(pins_ok),
                         'packages': [{k: p[k] for k in ('name', 'url', 'rev')} for p in packages],
                         'mathlib_revision': mathlib['rev'],
                         'exactly_one_lakefile': sum((ROOT / name).exists() for name in ('lakefile.toml', 'lakefile.lean')) == 1,
                         'publication_default_target': 'PalomarSolution' in lake['defaultTargets']},
        'ci': {'workflow': '.github/workflows/verify.yml', 'runner': workflow['jobs']['verify']['runs-on'],
               'permissions': workflow.get('permissions'), 'actions': actions,
               'actions_full_sha_pinned': all(re.fullmatch(r'[^@]+@[0-9a-f]{40}', a) for a in actions),
               'lean_action_inputs_exist_at_pin': set(lean_step['with']) <= lean_action['inputs'].keys(),
               'observed_execution': 'not assessed by this script; configuration checked only'},
        'administrative': {'root_license_files': license_files,
                           'root_formalization_yaml_present': (ROOT / 'formalization.yaml').is_file(),
                           'confirmed_human_authors': 'not verified by this script',
                           'confirmed_human_maintainers': 'not verified by this script',
                           'public_repository_and_final_commit': 'not verified by this script',
                           'submitter_authorization_relationship': 'not verified by this script'},
        'configuration_sha256': {name: sha((ROOT / name).read_bytes()) for name in config_files},
        'sources': snapshot,
    }
    (HERE / 'STATIC_PREFLIGHT.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    summary = {k: v for k, v in report.items() if k not in {'sources', 'configuration_sha256'}}
    (HERE / 'STATIC_PREFLIGHT_SUMMARY.json').write_text(json.dumps(summary, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(summary, indent=2, ensure_ascii=False))


if __name__ == '__main__':
    main()
