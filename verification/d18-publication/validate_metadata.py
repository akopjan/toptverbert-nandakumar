#!/usr/bin/env python3
"""Validate this project's metadata offline and snapshot existing gate reports.

Exit 0: schema and implemented local profile checks pass.
Exit 1: metadata is invalid/incomplete (expected for the unresolved draft).
Exit 2: an input, cache-integrity or parsing error prevented validation.
No Lean process, remote workflow, network request or licence detector is run.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import importlib.metadata
import json
from pathlib import Path
import re
import sys

import jsonschema
import yaml

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REFERENCES = HERE / 'official-references'
RELATIONSHIPS = {'formalizes', 'adapts', 'independently-proves', 'background', 'other'}
SOURCE_TYPES = {'paper', 'book', 'web discussion', 'folklore', 'original-proof', 'other'}
SUBSTANTIVE = {'formalizes', 'adapts', 'independently-proves'}
GATES = {
    'main_build_and_owner_audit': 'verification/d18-final-retry/results.json',
    'cumulative_source_rebuild': 'verification/d18-clean-final/results.json',
    'compiled_interface': 'verification/d18-compiled-interface/results.json',
    'independent_kernels': 'verification/d18-kernels/results.json',
    'approved_con_ron_replay': 'verification/d18-approved-con-ron/results.json',
    'local_sandboxed_comparator': 'verification/d18-comparator/results.json',
    'dependency_integrity': 'verification/d18-dependencies/results.json',
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def local_name(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT))
    except ValueError:
        return str(path.resolve())


class UniqueKeyLoader(yaml.SafeLoader):
    """Palomar forbids duplicate mapping keys and YAML merge keys."""


def unique_mapping(loader: UniqueKeyLoader, node: yaml.MappingNode, deep: bool = False) -> dict:
    result = {}
    for key_node, value_node in node.value:
        if key_node.tag == 'tag:yaml.org,2002:merge':
            raise ValueError('YAML merge keys are not permitted')
        key = loader.construct_object(key_node, deep=deep)
        try:
            if key in result:
                raise ValueError(f'Duplicate YAML mapping key: {key!r}')
        except TypeError as error:
            raise ValueError('YAML mapping keys must be scalar/hashable') from error
        result[key] = loader.construct_object(value_node, deep=deep)
    return result


UniqueKeyLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, unique_mapping)


def no_external_references(value: object) -> None:
    """Reject any schema reference that could initiate a remote lookup."""
    if isinstance(value, dict):
        for key, item in value.items():
            if key in {'$ref', '$dynamicRef', '$recursiveRef'}:
                if not isinstance(item, str) or not item.startswith('#'):
                    raise ValueError(f'Nonlocal schema reference is forbidden offline: {item!r}')
            no_external_references(item)
    elif isinstance(value, list):
        for item in value:
            no_external_references(item)


def gate_snapshot(relative: str) -> dict:
    path = ROOT / relative
    if not path.is_file():
        return {'path': relative, 'record_available': False,
                'qualification': 'No execution status is inferred from an absent report.'}
    data = path.read_bytes()
    result = {'path': relative, 'record_available': True, 'sha256': digest(data)}
    try:
        record = json.loads(data)
        keys = (
            'outcome', 'component_outcome', 'started_utc', 'finished_utc',
            'exit_code', 'driver_exit_code', 'checker_exit_code', 'elapsed_seconds',
            'checker_elapsed_seconds', 'stage_exit_codes', 'audit_summary',
            'sources_unchanged', 'input_bytes_unchanged', 'inputs_unchanged',
            'proof_inputs_unchanged', 'export_unchanged_during_kernel_checks',
            'types_compared', 'definition_values_compared', 'source_module_count',
            'export_sha256', 'export_size_bytes', 'permitted_axioms',
            'export_unchanged', 'checker_unchanged', 'same_export_and_declaration_records',
            'approved_release', 'approved_release_commit', 'approved_binary_sha256',
            'full_palomar_workflow', 'registry_acceptance', 'official_comparator',
            'local_sandboxed_comparator_passed', 'bwrap_mount_failure_observed',
            'sandbox_bypassed', 'theorem_proof_bodies_compared',
            'official_positive_negative_controls_run', 'declarations_sha256',
        )
        result['reported'] = {key: record[key] for key in keys if key in record}
        if isinstance(record.get('steps'), list):
            result['reported']['steps'] = [
                {key: step[key] for key in ('label', 'exit_code', 'elapsed_seconds') if key in step}
                for step in record['steps']]
        if 'declarations' in record:
            result['reported']['selected_declarations'] = record['declarations']
        if 'export_structure' in record:
            result['reported']['export_counts'] = record['export_structure'].get('declaration_record_counts')
        for key in ('input_sha256', 'input_sha256_before'):
            if isinstance(record.get(key), dict):
                result['reported'][key + '_count'] = len(record[key])
    except (ValueError, TypeError, AttributeError) as error:
        result['read_error'] = str(error)
        result['qualification'] = 'No execution status is inferred from an unreadable report.'
    return result


def validate(metadata_path: Path) -> dict:
    metadata_bytes = metadata_path.read_bytes()
    if len(metadata_bytes) > 256 * 1024:
        raise ValueError('Metadata exceeds the 256 KiB policy limit')
    metadata = yaml.load(metadata_bytes.decode('utf-8'), Loader=UniqueKeyLoader)
    manifest_bytes = (REFERENCES / 'DOWNLOADS.json').read_bytes()
    manifest = {item['file']: item for item in json.loads(manifest_bytes)}
    cached = {}
    reference_records = {}
    for name in ('formalization-v0.4.schema.json', 'arxiv-categories.json', 'msc2020-codes.json'):
        data = (REFERENCES / name).read_bytes()
        expected = manifest[name]
        if expected.get('outcome') != 'downloaded' or digest(data) != expected['sha256']:
            raise ValueError(f'Cached official reference does not match DOWNLOADS.json: {name}')
        cached[name] = json.loads(data)
        reference_records[name] = {'path': local_name(REFERENCES / name),
                                   'sha256': digest(data), 'bytes': len(data), 'url': expected['url']}
    schema = cached['formalization-v0.4.schema.json']
    no_external_references(schema)
    errors = sorted(jsonschema.Draft202012Validator(schema).iter_errors(metadata),
                    key=lambda error: tuple(map(str, error.absolute_path)))
    schema_errors = [{'path': '.'.join(map(str, error.absolute_path)),
                      'validator': error.validator, 'message': error.message} for error in errors]
    profile_errors = []

    def require(ok: bool, field: str, message: str) -> None:
        if not ok:
            profile_errors.append({'path': field, 'message': message})

    def nonempty(value: object) -> bool:
        return isinstance(value, str) and bool(value.strip())

    obj = metadata if isinstance(metadata, dict) else {}
    project = obj.get('project', {})
    project = project if isinstance(project, dict) else {}
    require(obj.get('version') == 'v0.4', 'version', 'This release uses the v0.4 metadata profile.')
    for field, bound in (('name', 300), ('description', 10000)):
        value = project.get(field)
        require(nonempty(value) and len(value) <= bound, 'project.' + field,
                f'A nonempty string of at most {bound} characters is required.')
    for field in ('authors', 'responsible_maintainers'):
        value = project.get(field)
        require(isinstance(value, list) and bool(value) and all(nonempty(x) for x in value),
                'project.' + field, 'A nonempty list of confirmed human name strings is required; identity is not verified by this script.')
    require(nonempty(project.get('license')), 'project.license', 'An exact, nonempty project SPDX identifier is required.')
    license_pattern = re.compile(r'(LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(\.(md|markdown|txt))?', re.I)
    license_files = sorted(path.name for path in ROOT.iterdir() if license_pattern.fullmatch(path.name))
    require(len(license_files) == 1, 'root_license_file', 'Exactly one conventional root licence file is required.')
    if len(license_files) == 1:
        license_path = ROOT / license_files[0]
        require(license_path.is_file() and not license_path.is_symlink(), 'root_license_file', 'The licence must be a regular nonsymlink file.')
        if license_path.is_file() and not license_path.is_symlink():
            license_bytes = license_path.read_bytes()
            require(0 < len(license_bytes) <= 1024 * 1024, 'root_license_file', 'The licence must be nonempty and at most 1 MiB.')
            try:
                license_bytes.decode('utf-8')
            except UnicodeError:
                require(False, 'root_license_file', 'The licence must be UTF-8 text.')

    classification = obj.get('classification', {})
    classification = classification if isinstance(classification, dict) else {}
    classification_records = {}
    for field, minimum, filename in (('arxiv', 1, 'arxiv-categories.json'), ('msc2020', 0, 'msc2020-codes.json')):
        values = classification.get(field, [])
        valid_list = isinstance(values, list) and all(isinstance(x, str) for x in values)
        require(valid_list and minimum <= len(values) <= 8 and len(set(values)) == len(values),
                'classification.' + field, f'Use {minimum}–8 distinct taxonomy codes.')
        if valid_list:
            taxonomy = cached[filename]
            classification_records[field] = {code: taxonomy.get(code) for code in values}
            for code in values:
                require(code in taxonomy, 'classification.' + field, f'Unknown cached taxonomy code: {code}')

    sources = obj.get('sources', [])
    require(isinstance(sources, list) and bool(sources), 'sources', 'A nonempty source list is required.')
    source_records = sources if isinstance(sources, list) else []
    for index, source in enumerate(source_records):
        source = source if isinstance(source, dict) else {}
        require(source.get('relationship') in RELATIONSHIPS, f'sources.{index}.relationship', 'A recognized nonempty source relationship is required.')
        require('type' not in source or source['type'] in SOURCE_TYPES, f'sources.{index}.type', 'Use a type from the Palomar policy vocabulary.')
    source_maps = [source for source in source_records if isinstance(source, dict)]
    original = any(source.get('type') == 'original-proof' for source in source_maps)
    original_valid = original and all(source.get('relationship') in {'background', 'other'} for source in source_maps) and all(source.get('relationship') == 'other' for source in source_maps if source.get('type') == 'original-proof')
    source_based_valid = not original and any(source.get('relationship') in SUBSTANTIVE for source in source_maps)
    require(original_valid or source_based_valid, 'sources', 'The source list must consistently declare original or source-based provenance.')

    automation = obj.get('automation', {})
    methods = automation.get('methods', []) if isinstance(automation, dict) else []
    require(isinstance(methods, list) and bool(methods) and all(isinstance(x, dict) and nonempty(x.get('method')) for x in methods),
            'automation.methods', 'A nonempty list of methods is required.')
    review = obj.get('review', {})
    require(isinstance(review, dict) and nonempty(review.get('status')), 'review.status', 'An honest nonempty review status is required.')

    comparator_bytes = (ROOT / 'comparator.json').read_bytes()
    comparator = json.loads(comparator_bytes)
    status = obj.get('status', {})
    main_results = status.get('main_results', []) if isinstance(status, dict) else []
    named = [item.get('declaration') for item in main_results if isinstance(item, dict)] if isinstance(main_results, list) else []
    valid = not schema_errors and not profile_errors
    return {
        'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'result': 'offline-metadata-checks-passed' if valid else 'metadata-invalid-or-incomplete',
        'exit_code': 0 if valid else 1,
        'scope': 'Offline schema and stated profile checks only; existing gate reports are read and hashed, never executed or assigned inferred pending statuses.',
        'metadata_path': local_name(metadata_path), 'draft_sha256': digest(metadata_bytes), 'draft_bytes': len(metadata_bytes),
        'schema_sha256': reference_records['formalization-v0.4.schema.json']['sha256'],
        'reference_inputs': reference_records, 'reference_manifest_sha256': digest(manifest_bytes),
        'validator_sha256': digest(Path(__file__).read_bytes()),
        'requirements_sha256': digest((HERE / 'requirements.txt').read_bytes()),
        'runtime': {'python': sys.version.split()[0], 'PyYAML': importlib.metadata.version('PyYAML'),
                    'jsonschema': importlib.metadata.version('jsonschema')},
        'schema_errors': schema_errors, 'profile_errors': profile_errors,
        'classification': classification_records,
        'derived_result_origin': 'original' if original_valid else 'source-based' if source_based_valid else None,
        'root_license_files': license_files,
        'project_alignment': {'comparator_sha256': digest(comparator_bytes), 'comparator_theorems': comparator['theorem_names'],
                              'metadata_main_results': named, 'main_results_exactly_match_comparator': named == comparator['theorem_names'],
                              'qualification': 'Main results are optional in the official schema; this reports alignment without imposing a new Palomar rule.'},
        'gates': {name: gate_snapshot(path) for name, path in GATES.items()},
        'not_verified': ['Human identities, authorship and submission authority', 'Project licence ownership and official SPDX-content detection',
                         'Bibliographic adequacy, priority and external peer review', 'Public repository permissions or registry acceptance'],
        'official_policy_coverage': 'This bounded offline check does not replace the official Palomar verifier or editorial review.',
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('metadata', nargs='?', type=Path, default=HERE / 'formalization.yaml.draft')
    parser.add_argument('--output', type=Path, default=HERE / 'METADATA_VALIDATION.json')
    args = parser.parse_args()
    if args.metadata.resolve() == args.output.resolve():
        parser.error('The report output must not overwrite the metadata input.')
    try:
        report = validate(args.metadata)
    except (OSError, ValueError, TypeError, KeyError, yaml.YAMLError, RecursionError) as error:
        report = {'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  'result': 'validation-input-error', 'exit_code': 2, 'error': str(error)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    print(json.dumps({key: report[key] for key in ('result', 'exit_code', 'schema_errors', 'profile_errors', 'error') if key in report},
                     indent=2, ensure_ascii=False))
    return report['exit_code']


if __name__ == '__main__':
    raise SystemExit(main())
