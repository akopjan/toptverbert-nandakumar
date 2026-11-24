#!/usr/bin/env python3
"""Fetch the canonical Lean release checker pinned by Palomar.

Only files below this script's directory are written. The full compressed
archive is hashed before extraction; no bundled toolchain is installed.
"""
from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
import hashlib
import json
import os
import shutil
import tarfile
import time
import urllib.request
import urllib.parse

import zstandard

ROOT = Path(__file__).resolve().parent
MANIFEST = Path('/workspace/scratch/9db1b532943d/akopyan-completion/verification/d18-publication/official-references/PalomarSubmission-checker-revisions.json')
TOOLCHAIN = 'leanprover/lean4:v4.35.0'
USER_AGENT = 'Lean-proof-verification'


def utc():
    return datetime.now(timezone.utc).isoformat()


def get_json(url, filename):
    request = urllib.request.Request(url, headers={
        'User-Agent': USER_AGENT, 'Accept': 'application/vnd.github+json'})
    with urllib.request.urlopen(request, timeout=40) as response:
        raw = response.read()
    (ROOT / filename).write_bytes(raw)
    return json.loads(raw)


def sha256_file(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


report = {
    'started_utc': utc(),
    'source_toolchain': TOOLCHAIN,
    'purpose': 'Supplemental con-ron component verification; not Palomar registry acceptance.',
    'official_manifest_source': str(MANIFEST),
    'outcome': 'in-progress',
}

try:
    manifest_raw = MANIFEST.read_bytes()
    (ROOT / 'official-checker-revisions.json').write_bytes(manifest_raw)
    report['official_manifest_sha256'] = hashlib.sha256(manifest_raw).hexdigest()
    expected = json.loads(manifest_raw)['con_ron'][TOOLCHAIN]
    report['expected'] = expected
    tag = expected['release_tag']
    release = json.loads((ROOT / 'official-release.json').read_text())
    assert release['tag_name'] == tag
    ref = get_json(
        f'https://api.github.com/repos/leanprover/lean4/git/ref/tags/{tag}',
        'official-tag-ref.json')
    obj = ref['object']
    if obj['type'] == 'tag':
        tag_object = get_json(obj['url'], 'official-tag-object.json')
        obj = tag_object['object']
    assert obj['type'] == 'commit'
    report['actual_release_commit'] = obj['sha']
    assert obj['sha'] == expected['release_commit'], 'Release commit mismatch'
    asset_name = f'lean-{tag.removeprefix("v")}-linux.tar.zst'
    asset = next(a for a in release['assets'] if a['name'] == asset_name)
    url = asset['browser_download_url']
    canonical = f'https://github.com/leanprover/lean4/releases/download/{tag}/{asset_name}'
    assert url == canonical, 'Unexpected download URL'
    assert asset['digest'] == 'sha256:' + expected['archive_sha256']
    report['canonical_download_url'] = url
    report['release_page'] = release['html_url']
    report['expected_archive_size'] = asset['size']
    archive_path = ROOT / asset_name
    request = urllib.request.Request(url, headers={'User-Agent': USER_AGENT})
    digest = hashlib.sha256()
    size = 0
    last_progress = time.monotonic()
    print('Downloading canonical archive:', url, flush=True)
    with urllib.request.urlopen(request, timeout=40) as response:
        report['download_http_status'] = response.status
        final_url = urllib.parse.urlsplit(response.geturl())
        report['resolved_download_location_without_query'] = urllib.parse.urlunsplit(
            (final_url.scheme, final_url.netloc, final_url.path, '', ''))
        report['download_headers'] = {
            key: response.headers.get(key)
            for key in ('Content-Length', 'Content-Type', 'ETag', 'Last-Modified')
        }
        with archive_path.open('wb') as out:
            while True:
                block = response.read(8 * 1024 * 1024)
                if not block:
                    break
                out.write(block)
                digest.update(block)
                size += len(block)
                now = time.monotonic()
                if now - last_progress >= 10:
                    print(f'Downloaded {size}/{asset["size"]} bytes', flush=True)
                    last_progress = now
    report['actual_archive_size'] = size
    report['actual_archive_sha256'] = digest.hexdigest()
    assert size == asset['size'], 'Archive size mismatch'
    assert digest.hexdigest() == expected['archive_sha256'], 'Archive SHA-256 mismatch'
    print('Full archive SHA-256 matched.', flush=True)

    extracted = []
    binary_path = ROOT / 'bin' / 'con-ron'
    with archive_path.open('rb') as compressed:
        with zstandard.ZstdDecompressor().stream_reader(compressed) as stream:
            with tarfile.open(fileobj=stream, mode='r|') as tar:
                for member in tar:
                    parts = PurePosixPath(member.name).parts
                    is_binary = len(parts) == 3 and parts[-2:] == ('bin', 'con-ron')
                    is_licence = len(parts) == 2 and parts[-1] in ('LICENSE', 'LICENSES', 'NOTICE')
                    if not (is_binary or is_licence):
                        continue
                    assert member.isfile(), f'Expected regular file: {member.name}'
                    destination = binary_path if is_binary else ROOT / parts[-1]
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    source = tar.extractfile(member)
                    assert source is not None
                    with source, destination.open('wb') as out:
                        shutil.copyfileobj(source, out, 1024 * 1024)
                    extracted.append({
                        'archive_member': member.name,
                        'local_file': str(destination.relative_to(ROOT)),
                        'size': member.size,
                        'sha256': sha256_file(destination),
                    })
                    print('Extracted', member.name, member.size, 'bytes', flush=True)
    assert binary_path.is_file(), 'Archive contains no bin/con-ron'
    report['actual_binary_sha256'] = sha256_file(binary_path)
    assert report['actual_binary_sha256'] == expected['binary_sha256'], 'Binary SHA-256 mismatch'
    os.chmod(binary_path, 0o755)
    report['extracted'] = extracted
    report['binary_path'] = str(binary_path)
    report['archive_path'] = str(archive_path)
    report['outcome'] = 'official-archive-and-checker-hashes-verified'
    report['checker_executed'] = False
    print('Official binary SHA-256 matched:', binary_path, flush=True)
except Exception as error:
    report['outcome'] = 'failed'
    report['error_type'] = type(error).__name__
    report['error'] = str(error)
    print(type(error).__name__ + ': ' + str(error), flush=True)
finally:
    report['finished_utc'] = utc()
    (ROOT / 'DOWNLOAD_VERIFICATION.json').write_text(json.dumps(report, indent=2) + '\n')

raise SystemExit(0 if report['outcome'] == 'official-archive-and-checker-hashes-verified' else 1)
