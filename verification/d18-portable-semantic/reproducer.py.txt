#!/usr/bin/env python3
"""Reproduce the archived Mathlib-only semantic diagnostic in a new directory.

This adapter compiles the two exact preserved sources in their original order.
It does not rebuild the project, change its specification, or run an external
proof kernel or the official Palomar Comparator. The pinned project and its
already-built objects must be present.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

PROJECT = Path(__file__).resolve().parents[2]
VERIFICATION = PROJECT / "verification"
ARCHIVE = VERIFICATION / "d18-extension-2026-11-24"
GATE = VERIFICATION / "d18-final-retry/source-before.json"
COMPILED = VERIFICATION / "d18-compiled-interface/results.json"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DIAGNOSTICS = {
    "SemanticReference": (
        "SEMANTIC_SCOPE_REFERENCE.lean.txt",
        "aecc193d3e92f3041b68b573f5a90bd98a0ce5eb2e00114fdbff3a2311d39a79",
    ),
    "SemanticScopeCheck": (
        "SEMANTIC_SCOPE_CHECK.lean.txt",
        "b895d9cdb765e0fb67d3e11acf9665393d6264fcc44a5ab8150813468504c2a9",
    ),
}
THEOREMS = [
    "SemanticScopeCheck.originalA",
    "SemanticScopeCheck.directHeightBridge",
    "SemanticScopeCheck.originalHeight",
    "SemanticScopeCheck.finalB",
    "SemanticScopeCheck.euclideanA",
]
WITNESSES = [
    "SemanticReference.sixVertices_mem",
    "SemanticReference.sixVertices_disjoint",
    "SemanticReference.matching_exists",
]
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def relative(path: Path) -> str:
    return path.relative_to(PROJECT).as_posix()


def local_file(name: str) -> Path:
    path = (PROJECT / name).resolve()
    if not path.is_relative_to(PROJECT) or not path.is_file():
        raise RuntimeError(f"Missing or non-project input: {name}")
    return path


def hashes(paths: list[Path]) -> dict[str, str]:
    return {relative(path): digest(path) for path in sorted(set(paths))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir", required=True,
        help="A NEW directory under verification/, relative to the project root",
    )
    args = parser.parse_args()
    output = (PROJECT / args.output_dir).resolve()
    if output == VERIFICATION or not output.is_relative_to(VERIFICATION):
        parser.error("Output must be a new strict subdirectory of verification/")
    if output.exists():
        parser.error("Refusing to reuse an existing output directory")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.mkdir()

    report: dict = {
        "outcome": "verification-in-progress",
        "scope": "Exact archived Mathlib-only semantic references, then actual proof checks",
        "started_utc": utc(),
        "project": str(PROJECT),
        "output_directory": relative(output),
        "adapter_command": [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]],
        "working_directory": str(Path.cwd()),
        "official_comparator": False,
        "external_proof_kernel_replay": False,
        "project_rebuilt": False,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "checked_theorems": THEOREMS,
        "nonvacuity_witnesses": WITNESSES,
        "stages": [],
    }
    before: dict[str, str] | None = None
    bound: list[Path] = []
    tools: dict[str, Path] = {}

    def save() -> None:
        write_json(output / "results.json", report)

    def run(label: str, command: list[str], cwd: Path, env: dict[str, str]) -> str:
        start = time.monotonic()
        print(f"Starting {label}", flush=True)
        completed = subprocess.run(
            command, cwd=cwd, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        log = output / f"{label}.log"
        log.write_text(completed.stdout, encoding="utf-8")
        (output / f"{label}.exit").write_text(f"{completed.returncode}\n")
        report["stages"].append({
            "label": label, "command": command, "cwd": str(cwd),
            "exit_code": completed.returncode,
            "seconds": round(time.monotonic() - start, 3),
            "log": log.name,
        })
        save()
        if completed.returncode:
            raise RuntimeError(f"{label} failed with exit {completed.returncode}; see {log.name}")
        return completed.stdout.strip()

    save()
    try:
        archived = {}
        for module, (filename, expected) in DIAGNOSTICS.items():
            source = ARCHIVE / filename
            if digest(source) != expected:
                raise RuntimeError(f"Archived diagnostic changed: {filename}")
            copied = output / f"{module}.lean"
            shutil.copyfile(source, copied)
            archived[module] = {
                "preserved_source": relative(source),
                "copied_source": copied.name,
                "sha256": expected,
            }
        report["diagnostics"] = archived
        shutil.copyfile(Path(__file__).resolve(), output / "reproducer.py.txt")

        gate = json.loads(GATE.read_text())
        expected_inputs = gate["input_sha256"]
        bound = [local_file(name) for name in expected_inputs]
        changed_from_gate = [
            name for name, expected in expected_inputs.items()
            if digest(local_file(name)) != expected
        ]
        if changed_from_gate:
            raise RuntimeError("Frozen release inputs differ from the successful gate: " +
                               ", ".join(changed_from_gate))
        compiled = json.loads(COMPILED.read_text())
        closure = compiled["proof_project_imports"]
        if "Solution" not in closure or "AkopyanResearch.Completion.DimensionEighteen" not in closure:
            raise RuntimeError("Recorded proof import closure is incomplete")
        if "Challenge" in closure or len(closure) != len(set(closure)):
            raise RuntimeError("Unexpected Challenge import or duplicate closure module")
        for module in closure:
            if not isinstance(module, str) or not MODULE.fullmatch(module):
                raise RuntimeError("Invalid recorded project module name")
            bound.append(local_file(module.replace(".", "/") + ".lean"))
            for suffix in (".olean", ".olean.private", ".olean.server"):
                name = ".lake/build/lib/lean/" + module.replace(".", "/") + suffix
                bound.append(local_file(name))
        bound.extend([
            GATE, COMPILED, Path(__file__).resolve(),
            ARCHIVE / "SEMANTIC_SCOPE_RESULTS.json",
            ARCHIVE / "SEMANTIC_SCOPE_RUNNER.py.txt",
            *[ARCHIVE / entry[0] for entry in DIAGNOSTICS.values()],
        ])
        before = hashes(bound)
        write_json(output / "input-sha256-before.json", before)
        report["frozen_release_inputs_matched"] = len(expected_inputs)
        report["bound_project_import_closure"] = closure
        report["bound_project_object_count"] = 3 * len(closure)

        launcher = shutil.which("lake")
        if not launcher:
            raise RuntimeError("lake is not on PATH; install/select the pinned toolchain first")
        # Preserve the launcher's name: an elan lake proxy may resolve to elan.
        lake = Path(launcher).absolute()
        env = os.environ.copy()
        version = run("lean-version", [str(lake), "env", "lean", "--version"], PROJECT, env)
        pin = (PROJECT / "lean-toolchain").read_text().strip()
        match = re.fullmatch(r"leanprover/lean4:v(\d+\.\d+\.\d+)", pin)
        if not match or not version.startswith(f"Lean (version {match.group(1)},"):
            raise RuntimeError(f"Toolchain mismatch: {pin!r}; installed {version!r}")
        prefix = Path(run(
            "lean-prefix", [str(lake), "env", "lean", "--print-prefix"], PROJECT, env
        )).resolve()
        lean = prefix / "bin/lean"
        actual_lake = prefix / "bin/lake"
        if not lean.is_file() or not actual_lake.is_file():
            raise RuntimeError("lake did not select an installed Lean toolchain")
        lake_version = run("lake-version", [str(lake), "--version"], PROJECT, env)
        path_json = run(
            "lake-search-path",
            [str(lake), "env", sys.executable, "-c",
             "import json,os; print(json.dumps(os.environ.get('LEAN_PATH', '')))"],
            PROJECT, env,
        )
        raw_paths = json.loads(path_json)
        if not isinstance(raw_paths, str) or not raw_paths:
            raise RuntimeError("lake returned no LEAN_PATH")
        search_paths = [
            (PROJECT / item).resolve() if not Path(item).is_absolute() else Path(item).resolve()
            for item in raw_paths.split(os.pathsep) if item
        ]
        project_objects = (PROJECT / ".lake/build/lib/lean").resolve()
        if project_objects not in search_paths:
            raise RuntimeError("lake search path does not contain the project's built objects")
        manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
        package_root = PROJECT / manifest["packagesDir"]
        dependency_roots = [(package_root / entry["name"]).resolve() for entry in manifest["packages"]]
        dependency_paths = [
            path for path in search_paths
            if path.is_relative_to(prefix) or
               any(path.is_relative_to(root) for root in dependency_roots)
        ]
        unexpected_paths = [
            str(path) for path in search_paths
            if path != project_objects and path not in dependency_paths
        ]
        if unexpected_paths:
            raise RuntimeError("Unrecognized Lean import paths: " + ", ".join(unexpected_paths))
        mathlib = next(entry for entry in manifest["packages"] if entry["name"] == "mathlib")
        mathlib_root = (package_root / "mathlib").resolve()
        if not any(path.is_relative_to(mathlib_root) for path in dependency_paths):
            raise RuntimeError("Missing pinned Mathlib build path")
        if not (mathlib_root / ".lake/build/lib/lean/Mathlib.olean").is_file():
            raise RuntimeError("Compile or fetch the pinned Mathlib objects before this diagnostic")

        tools = {
            "lake_launcher": lake, "lake": actual_lake,
            "lean": lean, "python": Path(sys.executable),
        }
        for name in ("libleanshared.so", "libLake_shared.so"):
            library = prefix / "lib/lean" / name
            if library.is_file():
                tools[name] = library
        tool_before = {name: digest(path) for name, path in tools.items()}
        report.update({
            "lean_toolchain": pin, "lean_version": version, "lake_version": lake_version,
            "python_version": sys.version, "mathlib_rev": mathlib["rev"],
            "tool_paths": {name: str(path) for name, path in tools.items()},
            "tool_sha256_before": tool_before,
            "reference_direct_imports": ["Mathlib"],
            "checker_direct_imports": [
                "SemanticReference", "Solution", "AkopyanResearch.Completion.DimensionEighteen",
            ],
            "reference_excludes_project_object_path": True,
        })

        for module, paths in (
            ("SemanticReference", dependency_paths),
            ("SemanticScopeCheck", search_paths),
        ):
            stage_env = env.copy()
            # The only extra module is the fresh reference in this NEW directory.
            stage_env["LEAN_PATH"] = os.pathsep.join(map(str, [output, *paths]))
            report.setdefault("compilation_search_paths", {})[module] = stage_env["LEAN_PATH"]
            run(module, [
                str(lean), "-j", "1", "-o", str(output / f"{module}.olean"),
                str(output / f"{module}.lean"),
            ], output, stage_env)

        log = (output / "SemanticScopeCheck.log").read_text()
        parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, flags=re.S)
        axiom_results = {}
        for theorem in THEOREMS:
            matches = [
                values for name, values in parsed
                if name == theorem or name.endswith("." + theorem)
            ]
            if len(matches) != 1:
                raise RuntimeError(f"Missing or duplicate axiom output for {theorem}")
            used = {name.strip() for name in matches[0].split(",") if name.strip()}
            if not used <= ALLOWED_AXIOMS:
                raise RuntimeError(f"Unpermitted axiom in {theorem}: {sorted(used)}")
            axiom_results[theorem] = sorted(used)
        if len(parsed) != len(THEOREMS):
            raise RuntimeError("Unexpected axiom-output inventory")
        for witness in WITNESSES:
            if not re.search(r"^" + re.escape(witness) + r"(?:\s|:)", log, flags=re.M):
                raise RuntimeError(f"Missing nonvacuity witness output: {witness}")
        report["axiom_results"] = axiom_results

        for module, (_, expected) in DIAGNOSTICS.items():
            if digest(output / f"{module}.lean") != expected:
                raise RuntimeError(f"Copied diagnostic changed during compilation: {module}")
        after = hashes(bound)
        write_json(output / "input-sha256-after.json", after)
        report["input_bytes_unchanged"] = before == after
        tool_after = {name: digest(path) for name, path in tools.items()}
        report["tool_sha256_after"] = tool_after
        report["tool_bytes_unchanged"] = tool_before == tool_after
        if before != after or tool_before != tool_after:
            raise RuntimeError("A bound source, object, tool, or diagnostic changed during the run")
        report["generated_artifact_sha256"] = {
            path.name: digest(path) for path in sorted(output.iterdir())
            if path.is_file() and path.name != "results.json"
        }
        report["outcome"] = "PASS"
        report["finished_utc"] = utc()
        save()
        print(json.dumps({
            "outcome": "PASS", "checked_theorems": len(THEOREMS),
            "input_bytes_unchanged": True, "tool_bytes_unchanged": True,
            "output_directory": relative(output),
        }, indent=2), flush=True)
        return 0
    except Exception as error:
        report["outcome"] = "FAIL"
        report["error"] = str(error)
        report["finished_utc"] = utc()
        if before is not None:
            try:
                after = hashes(bound)
                write_json(output / "input-sha256-after.json", after)
                report["input_bytes_unchanged"] = before == after
            except Exception as hash_error:
                report["final_snapshot_error"] = str(hash_error)
        save()
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
