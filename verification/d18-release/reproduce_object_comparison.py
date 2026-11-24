#!/usr/bin/env python3
"""Compare two already-built release checkouts without rebuilding or exporting.

Python 3.11+ and the pinned Lake/Lean toolchain on PATH are required.
Relative --output-dir paths are relative to --main-project. The output must
be a new directory below that project's verification directory.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import time


INSPECTOR_SHA256 = "1b5338df8f1789b2d2bc2f070b649e381d4007c238ef8a01592466550d120d21"
HISTORICAL = "verification/d18-clean-final/object-comparison"
SUFFIXES = (".olean", ".olean.private", ".olean.server")
GATE_STAGES = {"structure", "provenance", "unit-tests", "build", "statement-audit", "audit"}
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def save(output: Path, name: str, data) -> None:
    (output / name).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def safe_relative(name: str) -> str:
    path = PurePosixPath(name)
    require(bool(path.parts) and not path.is_absolute() and ".." not in path.parts,
            f"Invalid recorded relative input: {name}")
    return path.as_posix()


def snapshot(roots: dict[str, Path], names: list[str]) -> dict:
    return {role: {name: sha(root / name) for name in names}
            for role, root in roots.items()}


def gate(path: Path) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    require(data.get("outcome") == "build-and-project-owner-audit-passed"
            and data.get("sources_unchanged") is True
            and set(data.get("stage_exit_codes", {})) == GATE_STAGES
            and set(data["stage_exit_codes"].values()) == {0},
            f"Missing successful unchanged six-stage build evidence: {path}")
    return data


def validate_reader_result(data: dict, modules: list[str]) -> dict:
    require(data.get("all_nonextension_fields_equal") is True
            and data.get("strict_expression_equality") is True
            and data.get("extension_payloads_compared") is False
            and data.get("modules_compared") == len(modules),
            "The inspector did not establish strict equality for the requested modules")
    records = data.get("records", [])
    require([r.get("module") for r in records] == modules,
            "Inspector module records do not match the exact requested inventory")
    totals = Counter()
    for record in records:
        parts = record.get("parts", [])
        require([p.get("part") for p in parts] == ["exported", "server", "private"],
                f"Missing or reordered module parts: {record.get('module')}")
        for part in parts:
            require(part.get("strict_constant_differences") == []
                    and part.get("main_declarations") == part.get("clean_declarations")
                    and all(part.get(key) is True for key in (
                        "constant_names_equal", "extra_constant_names_equal",
                        "module_flag_equal", "imports_equal",
                        "all_nonextension_fields_equal")),
                    f"Stored declaration or import mismatch: {record.get('module')}")
            totals[part["part"]] += part["main_declarations"]
    return dict(totals)


def run(args: argparse.Namespace) -> int:
    main = args.main_project.resolve()
    clean = args.clean_project.resolve()
    require(main.is_dir() and clean.is_dir() and main != clean,
            "Supply two distinct existing project directories")
    output = (main / args.output_dir).resolve()
    require(output.is_relative_to(main / "verification"),
            "The new output directory must be below MAIN/verification")
    require(not output.exists(), "Output directory already exists; historical evidence is never overwritten")
    output.mkdir(parents=True, exist_ok=False)
    roots = {"main": main, "clean": clean}
    report = {
        "scope": "Exact stored project declarations and imports in two already-built checkouts",
        "started_utc": utc(), "outcome": "comparison-in-progress",
        "main_project": str(main), "clean_project": str(clean),
        "output_directory": str(output), "python_version": sys.version,
        "project_rebuild_launched": False, "proof_export_launched": False,
        "heavy_export_or_kernel_check_launched": False,
        "extension_payloads_compared": False,
        "all_inputs_unchanged_during_comparison": None,
        "historical_evidence_unchanged": None,
        "tool_and_adapter_bytes_unchanged": None,
        "commands": [],
    }
    save(output, "results.json", report)
    before = None
    names = []
    evidence_paths = {}
    evidence_before = {}
    tool_paths = {}
    tool_before = {}
    diagnostic_paths = {}
    diagnostic_before = {}
    succeeded = False
    try:
        main_gate_path = main / "verification/d18-final-retry/results.json"
        clean_gate_path = main / "verification/d18-clean-final/results.json"
        kernel_path = main / "verification/d18-kernels/results.json"
        history = main / HISTORICAL
        inspector_source = history / "CompareModuleData.lean.txt"
        runner = Path(__file__).resolve()
        evidence_paths = {
            "main_gate": main_gate_path, "clean_gate": clean_gate_path,
            "final_kernel_report": kernel_path,
            **{f"historical/{p.relative_to(history).as_posix()}": p
               for p in sorted(history.rglob("*")) if p.is_file()},
        }
        require("historical/run_comparison.py.txt" in evidence_paths,
                "The original historical driver is missing")
        evidence_before = {name: sha(path) for name, path in evidence_paths.items()}
        save(output, "preserved-evidence-before.json", evidence_before)
        main_gate, clean_gate = gate(main_gate_path), gate(clean_gate_path)
        expected = main_gate.get("input_sha256", {})
        require(expected and expected == clean_gate.get("input_sha256"),
                "The successful main and clean gates do not bind identical source inputs")
        modules = main_gate.get("proof_modules", [])
        require(modules and modules == clean_gate.get("proof_modules")
                and len(modules) == len(set(modules))
                and all(MODULE_NAME.fullmatch(m) for m in modules)
                and set(modules) == set(main_gate.get("source_modules", [])) - {"Challenge"},
                "The build reports disagree about the exact proof-owner inventory")
        require(all(re.fullmatch(r"[0-9a-f]{64}", h) for h in expected.values()),
                "Invalid recorded source hash")
        source_names = [safe_relative(name) for name in expected]
        names = sorted(set(source_names) | {
            ".lake/build/lib/lean/" + module.replace(".", "/") + suffix
            for module in modules for suffix in SUFFIXES})
        before = snapshot(roots, names)
        save(output, "input-sha256-before.json", before)
        for role in roots:
            for name, digest in expected.items():
                require(before[role][name] == digest,
                        f"{role} source differs from the successful build: {name}")
        require(sha(inspector_source) == INSPECTOR_SHA256,
                "The preserved fixed module-data inspector has changed")
        historical_report = json.loads((history / "results.json").read_text(encoding="utf-8"))
        require(historical_report.get("module_data_reader_sha256") == INSPECTOR_SHA256,
                "The fixed inspector disagrees with the historical comparison")
        kernel = json.loads(kernel_path.read_text(encoding="utf-8"))
        require(kernel.get("outcome") == "all-components-accepted"
                and kernel.get("proof_inputs_unchanged") is True
                and kernel.get("export_unchanged_during_kernel_checks") is True,
                "The retained final kernel report is incomplete or unsuccessful")
        kernel_inputs = kernel.get("input_sha256", {})
        report.update({
            "proof_modules": modules, "module_count": len(modules),
            "source_input_count": len(expected),
            "source_inputs_match_successful_builds": True,
            "module_data_reader_sha256": INSPECTOR_SHA256,
            "kernel_record_outcome_at_snapshot": kernel["outcome"],
            "kernel_input_sha256_digest": hashlib.sha256(
                json.dumps(kernel_inputs, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
        })

        toolchain = (main / "lean-toolchain").read_text().strip()
        require(toolchain == (clean / "lean-toolchain").read_text().strip()
                and toolchain == "leanprover/lean4:v4.35.0",
                "Both projects must use this release's pinned Lean 4.35.0 toolchain")
        lake_name = shutil.which("lake")
        require(lake_name is not None, "lake is not available on PATH")
        # Preserve argv[0] for an elan proxy named lake; hashing follows symlinks.
        lake = Path(lake_name).absolute()
        tool_paths = {"adapter": runner, "lake_launcher": lake,
                      "python": Path(sys.executable).resolve()}
        tool_before = {name: sha(path) for name, path in tool_paths.items()}
        command = [str(lake), "env", "lean", "--print-prefix"]
        process = subprocess.run(command, cwd=main, capture_output=True, text=True, timeout=60)
        report["commands"].append({"purpose": "resolve pinned Lean through Lake", "command": command,
                                   "cwd": str(main), "exit_code": process.returncode,
                                   "stdout": process.stdout, "stderr": process.stderr})
        require(process.returncode == 0, "Lake could not resolve the pinned Lean toolchain")
        prefix = Path(process.stdout.strip()).resolve()
        lean = prefix / "bin/lean"
        pinned_lake = prefix / "bin/lake"
        require(lean.is_file() and os.access(lean, os.X_OK) and pinned_lake.is_file(),
                "Lake returned an invalid toolchain prefix")
        tool_paths.update({"lean": lean, "pinned_lake": pinned_lake})
        tool_before.update({name: sha(tool_paths[name]) for name in ("lean", "pinned_lake")})
        version_command = [str(lean), "--version"]
        version = subprocess.run(version_command, cwd=main, capture_output=True, text=True, timeout=30)
        report["commands"].append({"purpose": "check resolved Lean version", "command": version_command,
                                   "cwd": str(main), "exit_code": version.returncode,
                                   "stdout": version.stdout, "stderr": version.stderr})
        require(version.returncode == 0 and version.stdout.startswith("Lean (version 4.35.0,"),
                "The resolved Lean executable does not match lean-toolchain")
        report["toolchain"] = toolchain
        report["toolchain_prefix"] = str(prefix)
        report["tool_sha256"] = tool_before
        save(output, "tool-sha256-before.json", tool_before)

        records = []
        for module in modules:
            for suffix in SUFFIXES:
                name = ".lake/build/lib/lean/" + module.replace(".", "/") + suffix
                a, b = (main / name).read_bytes(), (clean / name).read_bytes()
                record = {"module": module, "suffix": suffix, "path": name,
                          "main_bytes": len(a), "clean_bytes": len(b),
                          "main_sha256": hashlib.sha256(a).hexdigest(),
                          "clean_sha256": hashlib.sha256(b).hexdigest(),
                          "byte_identical": a == b}
                require(record["main_sha256"] == before["main"][name]
                        and record["clean_sha256"] == before["clean"][name],
                        f"An object changed while being compared: {name}")
                require(kernel_inputs.get(name) == record["main_sha256"],
                        f"The main object does not match the final kernel export input: {name}")
                if suffix == ".olean.private" and a != b:
                    offsets = [i for i, (x, y) in enumerate(zip(a, b)) if x != y]
                    record["aligned_different_bytes"] = len(offsets)
                    record["different_offsets_from_end"] = [len(a) - i for i in offsets]
                records.append(record)
        save(output, "object-hashes.json", records)
        differing = sorted({record["module"] for record in records if not record["byte_identical"]})
        module_list = output / "differing-modules.txt"
        module_list.write_text("\n".join(differing) + "\n", encoding="utf-8")
        inspector = output / "CompareModuleData.lean"
        shutil.copyfile(inspector_source, inspector)
        require(sha(inspector) == INSPECTOR_SHA256, "Inspector copy changed")
        shutil.copyfile(runner, output / "reproduce_object_comparison.py.txt")
        diagnostic_paths = {"inspector": inspector, "module_list": module_list,
                            "adapter_copy": output / "reproduce_object_comparison.py.txt"}
        diagnostic_before = {name: sha(path) for name, path in diagnostic_paths.items()}
        save(output, "diagnostic-sha256-before.json", diagnostic_before)
        report.update({
            "objects_compared": len(records),
            "byte_identical_objects": sum(record["byte_identical"] for record in records),
            "different_objects": sum(not record["byte_identical"] for record in records),
            "differing_modules": differing,
            "differences_by_suffix": dict(Counter(record["suffix"] for record in records
                                                  if not record["byte_identical"])),
            "main_total_bytes": sum(record["main_bytes"] for record in records),
            "clean_total_bytes": sum(record["clean_bytes"] for record in records),
            "kernel_bound_object_count": len(records),
            "main_matches_kernel_bound_objects": True,
        })
        command = [str(lean), "-j1", "--run", str(inspector), str(main), str(clean),
                   str(module_list), str(output / "constant-comparison.json")]
        environment = os.environ.copy()
        environment["LEAN_NUM_THREADS"] = "1"
        started = time.monotonic()
        with (output / "constant-comparison.log").open("w", encoding="utf-8") as log:
            process = subprocess.run(command, cwd=output, env=environment, stdout=log,
                                     stderr=subprocess.STDOUT, timeout=300)
        elapsed = time.monotonic() - started
        (output / "constant-comparison.exit").write_text(str(process.returncode) + "\n")
        report["commands"].append({"purpose": "read stored module data", "command": command,
                                   "cwd": str(output), "exit_code": process.returncode,
                                   "environment": {"LEAN_NUM_THREADS": "1"}})
        report["module_data_exit_code"] = process.returncode
        report["module_data_seconds"] = round(elapsed, 3)
        require(process.returncode == 0, "The fixed module-data inspector failed")
        data = json.loads((output / "constant-comparison.json").read_text(encoding="utf-8"))
        report["strictly_compared_declarations_by_part"] = validate_reader_result(data, differing)
        report["all_stored_nonextension_fields_equal"] = True
        report["strict_expression_equality"] = True
        succeeded = True
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as error:
        report["error"] = f"{type(error).__name__}: {error}"
    finally:
        try:
            if before is not None:
                after = snapshot(roots, names)
                save(output, "input-sha256-after.json", after)
                report["all_inputs_unchanged_during_comparison"] = before == after
                report["changes_to_project_sources_or_objects"] = before != after
            if evidence_before:
                evidence_after = {name: sha(path) for name, path in evidence_paths.items()}
                save(output, "preserved-evidence-after.json", evidence_after)
                report["historical_evidence_unchanged"] = evidence_before == evidence_after
            if tool_before:
                tool_after = {name: sha(path) for name, path in tool_paths.items()}
                save(output, "tool-sha256-after.json", tool_after)
                report["tool_and_adapter_bytes_unchanged"] = tool_before == tool_after
            if diagnostic_before:
                diagnostic_after = {name: sha(path) for name, path in diagnostic_paths.items()}
                save(output, "diagnostic-sha256-after.json", diagnostic_after)
                report["diagnostic_inputs_unchanged"] = diagnostic_before == diagnostic_after
        except OSError as error:
            report["postcheck_error"] = f"{type(error).__name__}: {error}"
            succeeded = False
        succeeded = succeeded and all(report.get(key) is True for key in (
            "all_inputs_unchanged_during_comparison", "historical_evidence_unchanged",
            "tool_and_adapter_bytes_unchanged", "diagnostic_inputs_unchanged"))
        report["finished_utc"] = utc()
        report["outcome"] = ("same-declarations-different-metadata" if succeeded
                             and report.get("different_objects") else
                             "byte-identical-declarations" if succeeded else "comparison-failed")
        report["passed"] = succeeded
        save(output, "results.json", report)
    print(json.dumps({key: report.get(key) for key in (
        "outcome", "passed", "module_count", "objects_compared", "byte_identical_objects",
        "different_objects", "differences_by_suffix", "module_data_exit_code",
        "all_inputs_unchanged_during_comparison", "historical_evidence_unchanged",
        "tool_and_adapter_bytes_unchanged", "kernel_bound_object_count",
        "main_matches_kernel_bound_objects", "error")}, indent=2), flush=True)
    return 0 if succeeded else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--main-project", type=Path, required=True)
    parser.add_argument("--clean-project", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True,
                        help="New directory below MAIN/verification; relative paths use MAIN")
    args = parser.parse_args()
    try:
        return run(args)
    except (OSError, ValueError) as error:
        parser.exit(1, f"error: {error}\n")


if __name__ == "__main__":
    sys.exit(main())
