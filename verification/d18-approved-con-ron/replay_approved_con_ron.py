#!/usr/bin/env python3
"""Replay the final export with the exact Palomar-pinned con-ron binary.

This is a supplemental component check, not the Palomar registry workflow.
The completed ordinary-kernels report must describe exactly the supplied
export. The checker and export are hashed before and after the attempt.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
APPROVED_BINARY_SHA256 = "4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef"
APPROVED_ARCHIVE_SHA256 = "26b3cea1a006ad419215520b8668dcd3f6a9eeba1a123756563a739f9c6274b2"
APPROVED_COMMIT = "c9afcddf514a6772bd4d649f7cfc04eff0b9f15e"
APPROVED_RELEASE = "v4.36.0-rc1"
SOURCE_TOOLCHAIN = "leanprover/lean4:v4.35.0"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FINAL_THEOREMS = {
    "AkopyanSixfold.tverberg_counterexample",
    "AkopyanSixfold.almostSix_ninety",
    "AkopyanSixfold.convex_partition_counterexample_gt_17",
    "AkopyanResearch.ConcreteComparisonLifting.requiredRelativeLifting",
}
KINDS = ["axiom", "def", "opaque", "thm", "quot", "inductive"]


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def file_identity(path: Path) -> dict:
    stat = path.stat()
    return {
        "size": stat.st_size,
        "mtime_ns": stat.st_mtime_ns,
        "device": stat.st_dev,
        "inode": stat.st_ino,
    }


def inspect_export(path: Path, theorems: list[str], definitions: list[str]) -> dict:
    """Independently inspect all NDJSON records while hashing the exact bytes."""
    names = {0: ""}
    expected = {name: "thm" for name in theorems}
    expected.update({name: "def" for name in definitions})
    targets = {}
    axioms = set()
    counts: Counter[str] = Counter()
    digest = hashlib.sha256()
    byte_count = 0
    line_number = 0
    last_progress = time.monotonic()
    with path.open("rb") as handle:
        for line_number, line in enumerate(handle, 1):
            digest.update(line)
            byte_count += len(line)
            record = json.loads(line)
            require(isinstance(record, dict), f"Non-object export record at line {line_number}")
            if "in" in record:
                if "str" in record:
                    item = record["str"]
                    prefix, suffix = names[item["pre"]], item["str"]
                elif "num" in record:
                    item = record["num"]
                    prefix, suffix = names[item["pre"]], str(item["i"])
                else:
                    raise ValueError(f"Unknown name record at line {line_number}")
                names[record["in"]] = prefix + "." + suffix if prefix else suffix
            for kind in KINDS:
                if kind not in record:
                    continue
                counts[kind] += 1
                declaration = record[kind]
                if "name" not in declaration:
                    continue
                name = names[declaration["name"]]
                if kind == "axiom":
                    axioms.add(name)
                if name in expected:
                    require(name not in targets, f"Duplicate target declaration: {name}")
                    targets[name] = {
                        "kind": kind, "line": line_number,
                        "has_value": "value" in declaration,
                    }
            now = time.monotonic()
            if now - last_progress >= 30:
                print(f"Inspected {byte_count} bytes / {line_number} NDJSON records", flush=True)
                last_progress = now
    require(byte_count > 0, "The export is empty")
    for name, kind in expected.items():
        info = targets.get(name)
        require(info is not None and info["kind"] == kind and info["has_value"],
                f"Target lacks its actual exported {kind} body: {name}: {info}")
    require(axioms <= AXIOMS, f"Unpermitted export axioms: {sorted(axioms - AXIOMS)}")
    return {
        "sha256": digest.hexdigest(),
        "size_bytes": byte_count,
        "record_count": line_number,
        "structure": {
            "target_records": targets,
            "axioms": sorted(axioms),
            "declaration_record_counts": dict(counts),
        },
    }


def verify_acquisition_evidence() -> dict:
    manifest_file = ROOT / "official-checker-revisions.json"
    acquisition_file = ROOT / "DOWNLOAD_VERIFICATION.json"
    manifest = json.loads(manifest_file.read_bytes())
    acquisition = json.loads(acquisition_file.read_bytes())
    expected = {
        "release_tag": APPROVED_RELEASE,
        "release_commit": APPROVED_COMMIT,
        "archive_sha256": APPROVED_ARCHIVE_SHA256,
        "binary_sha256": APPROVED_BINARY_SHA256,
    }
    require(manifest["con_ron"][SOURCE_TOOLCHAIN] == expected,
            "Bundled official manifest does not contain the exact approved revision")
    require(acquisition["outcome"] == "official-archive-and-checker-hashes-verified",
            "Acquisition evidence does not report verified hashes")
    require(acquisition["expected"] == expected, "Acquisition expected revision differs")
    require(acquisition["actual_release_commit"] == APPROVED_COMMIT, "Acquisition commit differs")
    require(acquisition["actual_archive_sha256"] == APPROVED_ARCHIVE_SHA256,
            "Acquisition archive hash differs")
    require(acquisition["actual_binary_sha256"] == APPROVED_BINARY_SHA256,
            "Acquisition binary hash differs")
    require(acquisition["official_manifest_sha256"] == sha256_file(manifest_file),
            "Bundled official manifest differs from the acquired manifest")
    copied = json.loads((ROOT / "SOURCE_COPY_MANIFEST.json").read_bytes())
    hashes = {}
    for item in copied["copied_files"]:
        relative = Path(item["file"])
        require(not relative.is_absolute() and ".." not in relative.parts,
                "Invalid provenance file path")
        path = ROOT / relative
        require(path.is_file() and path.stat().st_size == item["size"],
                f"Missing or resized provenance evidence: {relative}")
        digest = sha256_file(path)
        require(digest == item["sha256"], f"Changed provenance evidence: {relative}")
        hashes[str(relative)] = digest
    hashes["SOURCE_COPY_MANIFEST.json"] = sha256_file(ROOT / "SOURCE_COPY_MANIFEST.json")
    return hashes


def completed_prior_report(raw: bytes) -> tuple[dict, list[str], list[str], dict]:
    prior = json.loads(raw)
    require(isinstance(prior, dict), "Kernels report is not a JSON object")
    require(prior.get("finished_utc") is not None, "Ordinary kernel checks are not finished")
    require(prior.get("outcome") in {
        "all-components-accepted", "one-or-more-components-unsuccessful"},
        f"Ordinary kernels report is unfinished or has changed inputs: {prior.get('outcome')}")
    require(prior.get("proof_inputs_unchanged") is True,
            "Ordinary checks did not establish unchanged proof inputs")
    require(prior.get("changed_inputs_during_verification") == [],
            "Ordinary checks report changed inputs")
    require(prior.get("export_unchanged_during_kernel_checks") is True,
            "Ordinary checks did not establish an unchanged export")
    require(set(prior.get("permitted_axioms", [])) == AXIOMS,
            "Ordinary report has a different axiom policy")
    require(prior.get("nanoda_unpermitted_axiom_hard_error") is True,
            "Ordinary NanoDa report lacks hard-error enforcement for unpermitted axioms")
    require(re.search(r"\bversion 4\.35\.0(?:,|\))",
                      prior.get("tool_versions", {}).get("lean", "")) is not None,
            "Ordinary report does not identify the supported Lean 4.35.0 compiler")
    steps = {}
    for step in prior.get("steps", []):
        label = step.get("label")
        require(label not in steps, f"Duplicate prior-check label: {label}")
        steps[label] = step
    for label in ["build", "declaration-audit", "export", "leanchecker", "nanoda"]:
        require(label in steps and steps[label].get("exit_code") == 0,
                f"Mandatory preceding component did not pass: {label}")
    require("con-ron" in steps and isinstance(steps["con-ron"].get("exit_code"), int),
            "The bundled con-ron attempt is not complete")
    theorems = prior.get("declarations")
    definitions = prior.get("definition_targets", [])
    require(isinstance(theorems, list) and all(isinstance(n, str) for n in theorems),
            "Invalid theorem list in ordinary report")
    require(isinstance(definitions, list) and all(isinstance(n, str) for n in definitions),
            "Invalid definition list in ordinary report")
    require(len(set(theorems)) == len(theorems) and len(set(definitions)) == len(definitions),
            "Duplicate selected declarations")
    require(not set(theorems).intersection(definitions), "Conflicting selected declaration kinds")
    require(FINAL_THEOREMS <= set(theorems), "The ordinary report does not select all four final theorems")
    require(prior.get("exported_declarations") == theorems + definitions,
            "Selected theorem/definition lists disagree with exported declarations")
    require(isinstance(prior.get("export_structure"), dict), "Ordinary report lacks export inspection")
    return prior, theorems, definitions, steps


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checker", required=True, type=Path,
                        help="Exact approved con-ron executable; verified by SHA-256")
    parser.add_argument("--export", required=True, type=Path,
                        help="Completed final .ndjson export already checked by the ordinary kernels")
    parser.add_argument("--kernels-report", required=True, type=Path,
                        help="Completed results.json from scripts/verify-selected-kernels.py")
    parser.add_argument("--output-dir", type=Path, default=ROOT,
                        help="Fresh evidence directory within this replay bundle")
    parser.add_argument("--timeout-seconds", type=int, default=1800,
                        help="Checker process limit; default 1800 seconds")
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    output = args.output_dir.expanduser().resolve()
    if not output.is_relative_to(ROOT):
        parser.error("--output-dir must be this bundle or a directory within it")
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "results.json"
    artifact_names = ["results.json", "con-ron.log", "con-ron.exit", "prior-kernels-results.json"]
    if any((output / name).exists() for name in artifact_names):
        parser.error("Replay evidence already exists; choose a fresh --output-dir within this bundle")
    report = {
        "scope": "Supplemental replay of the same final export with the official approved con-ron binary",
        "full_palomar_workflow": False,
        "registry_acceptance": False,
        "independent_challenge_comparison": False,
        "official_positive_negative_controls_run": False,
        "sandbox_note": "Uses the surrounding execution sandbox; does not reproduce the registry bwrap workflow.",
        "started_utc": utc(),
        "outcome": "preflight-in-progress",
        "checker_attempted": False,
        "source_toolchain": SOURCE_TOOLCHAIN,
        "approved_release": APPROVED_RELEASE,
        "approved_release_commit": APPROVED_COMMIT,
        "approved_binary_sha256": APPROVED_BINARY_SHA256,
        "verifier_sha256": sha256_file(Path(__file__).resolve()),
        "permitted_axioms": sorted(AXIOMS),
        "required_final_theorems": sorted(FINAL_THEOREMS),
        "jobs": 4,
        "timeout_seconds": args.timeout_seconds,
    }

    def save() -> None:
        temporary = report_path.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        temporary.replace(report_path)

    save()
    exit_code = 2
    try:
        checker = args.checker.expanduser().resolve(strict=True)
        export = args.export.expanduser().resolve(strict=True)
        prior_path = args.kernels_report.expanduser().resolve(strict=True)
        require(checker.is_file() and os.access(checker, os.X_OK), "Checker is not executable")
        require(export.is_file() and export.suffix == ".ndjson", "Expected a regular .ndjson export")
        require(prior_path.is_file(), "Expected a regular ordinary-kernels report")
        require(len({checker, export, prior_path}) == 3, "Input paths must be distinct")
        require(not any(path == output / name for path in [checker, export, prior_path]
                        for name in artifact_names), "An output artifact would overwrite an input")
        report["checker_path"] = str(checker)
        report["export_file"] = str(export)
        report["ordinary_kernels_report"] = str(prior_path)
        report["acquisition_evidence_sha256"] = verify_acquisition_evidence()
        report["checker_sha256_before"] = sha256_file(checker)
        require(report["checker_sha256_before"] == APPROVED_BINARY_SHA256,
                "Checker SHA-256 does not match the official approved executable")
        report["checker_identity_before"] = file_identity(checker)
        prior_raw = prior_path.read_bytes()
        report["ordinary_kernels_report_sha256"] = hashlib.sha256(prior_raw).hexdigest()
        prior, theorems, definitions, steps = completed_prior_report(prior_raw)
        (output / "prior-kernels-results.json").write_bytes(prior_raw)
        report["ordinary_kernel_exit_codes"] = {
            label: steps[label]["exit_code"] for label in ["leanchecker", "nanoda", "con-ron"]}
        report["ordinary_outcome"] = prior["outcome"]
        report["ordinary_export_sha256"] = prior["export_sha256"]
        report["declarations"] = theorems
        report["definition_targets"] = definitions
        report["exported_declarations"] = prior["exported_declarations"]
        report["export_identity_before_inspection"] = file_identity(export)
        print("Inspecting and hashing the final export without modifying it", flush=True)
        actual = inspect_export(export, theorems, definitions)
        report["export_sha256"] = actual["sha256"]
        report["export_size_bytes"] = actual["size_bytes"]
        report["export_record_count"] = actual["record_count"]
        report["export_structure"] = actual["structure"]
        require(actual["sha256"] == prior["export_sha256"], "Export differs from ordinary-kernels export")
        require(actual["size_bytes"] == prior["export_size_bytes"], "Export size differs from ordinary report")
        require(actual["structure"] == prior["export_structure"],
                "Actual declaration records differ from the ordinary export inspection")
        report["same_export_and_declaration_records"] = True
        report["export_identity_before_checker"] = file_identity(export)
        require(report["export_identity_before_checker"] == report["export_identity_before_inspection"],
                "Export changed while its records were inspected")
        require(sha256_file(checker) == APPROVED_BINARY_SHA256, "Checker changed during export inspection")
        command = [str(checker), "--jobs=4", str(export)]
        report["command"] = command
        report["outcome"] = "checker-in-progress"
        report["checker_attempted"] = True
        save()
        started = time.monotonic()
        print("Starting approved con-ron with --jobs=4", flush=True)
        timed_out = False
        with (output / "con-ron.log").open("wb") as handle:
            try:
                result = subprocess.run(command, stdin=subprocess.DEVNULL,
                                        stdout=handle, stderr=handle, cwd=output,
                                        timeout=args.timeout_seconds, check=False)
                checker_exit = result.returncode
            except subprocess.TimeoutExpired:
                timed_out = True
                checker_exit = 124
        (output / "con-ron.exit").write_text(str(checker_exit) + "\n", encoding="utf-8")
        report["checker_exit_code"] = checker_exit
        report["checker_timed_out"] = timed_out
        report["checker_elapsed_seconds"] = round(time.monotonic() - started, 3)
        report["checker_log"] = str((output / "con-ron.log").relative_to(ROOT))
        report["checker_log_sha256"] = sha256_file(output / "con-ron.log")
        print(f"Checker exited {checker_exit}; checking immutable inputs", flush=True)
        report["export_sha256_after_checker"] = sha256_file(export)
        report["checker_sha256_after"] = sha256_file(checker)
        report["ordinary_kernels_report_sha256_after"] = sha256_file(prior_path)
        report["export_unchanged"] = report["export_sha256_after_checker"] == report["export_sha256"]
        report["checker_unchanged"] = report["checker_sha256_after"] == APPROVED_BINARY_SHA256
        report["ordinary_report_unchanged"] = (
            report["ordinary_kernels_report_sha256_after"] == report["ordinary_kernels_report_sha256"])
        require(report["export_unchanged"], "Export changed during the checker attempt")
        require(report["checker_unchanged"], "Checker binary changed during the attempt")
        require(report["ordinary_report_unchanged"], "Ordinary-kernels report changed during the attempt")
        if timed_out:
            report["outcome"] = "approved-checker-timeout-unverified"
            exit_code = 124
        elif checker_exit == 0:
            report["outcome"] = "approved-con-ron-accepted-same-final-export"
            exit_code = 0
        else:
            report["outcome"] = "approved-con-ron-unsuccessful"
            exit_code = 1
    except KeyboardInterrupt:
        report["outcome"] = "interrupted-unverified"
        exit_code = 130
    except Exception as error:
        report["outcome"] = "replay-validation-failed" if report["checker_attempted"] else "preflight-failed"
        report["error_type"] = type(error).__name__
        report["error"] = str(error)
        print(type(error).__name__ + ": " + str(error), file=sys.stderr, flush=True)
        exit_code = 1 if report["checker_attempted"] else 2
    finally:
        report["driver_exit_code"] = exit_code
        report["finished_utc"] = utc()
        save()
    print(report["outcome"], flush=True)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
