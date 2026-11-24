#!/usr/bin/env python3
"""Build and export selected theorems/definitions, then run bundled kernel checkers.

This performs component checks, not the sandboxed Palomar Comparator workflow.
It does not compare the declarations with an independently specified Challenge.
It writes an audit file, build artifacts, and logs, and leaves proof sources
unchanged. The build ensures that recorded source hashes correspond to the
compiled modules being exported.

Example:
    python3 scripts/verify-selected-kernels.py Module Namespace.theorem_name \
        --output-dir verification/selected-kernels
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


AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
LEAN_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


def sha256(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def inspect_export(path: Path, targets: list[str], definition_targets: list[str] | None = None) -> dict:
    """Check record kinds and axiom names, not just exported type signatures.

    Name records follow the toolchain's LeanExport.Basic.dumpName format.
    The independent kernels below perform the actual term/type checking.
    """
    names = {0: ""}
    expected_kinds = {name: "thm" for name in targets}
    expected_kinds.update({name: "def" for name in definition_targets or []})
    target_set = set(expected_kinds)
    target_records = {}
    axioms = set()
    counts = Counter()
    with path.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            record = json.loads(line)
            if "in" in record:
                if "str" in record:
                    part = record["str"]
                    prefix, suffix = names[part["pre"]], part["str"]
                elif "num" in record:
                    part = record["num"]
                    prefix, suffix = names[part["pre"]], str(part["i"])
                else:
                    raise ValueError(f"Unknown name record at export line {line_number}")
                names[record["in"]] = prefix + "." + suffix if prefix else suffix
            for kind in ["axiom", "def", "opaque", "thm", "quot", "inductive"]:
                if kind not in record:
                    continue
                counts[kind] += 1
                declaration = record[kind]
                if "name" not in declaration:
                    continue
                name = names[declaration["name"]]
                if kind == "axiom":
                    axioms.add(name)
                if name in target_set:
                    target_records[name] = {"kind": kind, "line": line_number,
                                            "has_value": "value" in declaration}
    for target, expected_kind in expected_kinds.items():
        info = target_records.get(target)
        if info is None or info["kind"] != expected_kind or not info["has_value"]:
            raise ValueError(f"Selected target lacks an exported {expected_kind} body: {target}: {info}")
    forbidden = axioms.difference(AXIOMS)
    if forbidden:
        raise ValueError(f"Export contains axioms outside the whitelist: {sorted(forbidden)}")
    return {"target_records": target_records, "axioms": sorted(axioms),
            "declaration_record_counts": dict(counts)}


def local_dependency_closure(project: Path, module: str, lake: Path) -> tuple[list[str], dict, list]:
    """Use Lean's own import parser recursively, retaining project-local modules.

    External dependencies are pinned by lake-manifest.json and included as
    proof terms in the export as needed. This project's source layout maps
    Foo.Bar to Foo/Bar.lean and uses the standard Lake build directory.
    """
    build_root = (project / ".lake/build/lib/lean").resolve()
    pending = [module]
    visited = set()
    graph = {}
    commands = []
    while pending:
        current = pending.pop()
        if current in visited:
            continue
        visited.add(current)
        source = current.replace(".", "/") + ".lean"
        if not (project / source).is_file():
            raise ValueError(f"Cannot locate local module source: {source}")
        command = [str(lake), "env", "lean", "--deps", source]
        result = subprocess.run(command, cwd=project, text=True, capture_output=True)
        commands.append({"command": command, "exit_code": result.returncode,
                         "stdout": result.stdout, "stderr": result.stderr})
        if result.returncode != 0:
            raise ValueError(f"Lean dependency discovery failed for {source}: {result.stderr}")
        children = set()
        for line in result.stdout.splitlines():
            path = Path(line.strip()).resolve()
            if path.suffix != ".olean" or not path.is_relative_to(build_root):
                continue
            relative = path.relative_to(build_root).with_suffix("")
            child = ".".join(relative.parts)
            children.add(child)
            pending.append(child)
        graph[current] = sorted(children)
        print(f"Recorded dependencies of {current}", flush=True)
    return sorted(visited), graph, commands


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", help="Lean module to build and export, for example TableRealization")
    parser.add_argument("declarations", nargs="+", help="Fully qualified theorem names")
    parser.add_argument("--proof-module", action="append", default=[],
                        help="Owning module of a target, imported with `import all` (repeatable)")
    parser.add_argument("--definition", action="append", default=[],
                        help="Also print a definition used in the statement (repeatable)")
    parser.add_argument("--definition-target", action="append", default=[],
                        help="Export and check an actual definition body in addition to the theorems (repeatable)")
    parser.add_argument("--output-dir", default="verification/selected-kernels")
    parser.add_argument("--export-file", metavar="FILE_NDJSON",
                        help="Write the large export separately; logs remain in --output-dir")
    parser.add_argument("--reuse-dependency-discovery", metavar="RESULTS_JSON",
                        help="Reuse recorded Lean --deps results only if all source, configuration and pin hashes match")
    args = parser.parse_args()
    for name in [args.module, *args.declarations, *args.definition, *args.definition_target,
                 *args.proof_module]:
        if not LEAN_NAME.fullmatch(name):
            parser.error(f"Expected an ASCII Lean declaration/module name: {name!r}")
    if set(args.declarations).intersection(args.definition_target):
        parser.error("A declaration cannot be selected as both a theorem and a definition.")
    exported_declarations = list(dict.fromkeys([*args.declarations, *args.definition_target]))

    project = Path(__file__).resolve().parent.parent
    output = (project / args.output_dir).resolve()
    if not output.is_relative_to(project):
        parser.error("The output directory must lie inside this Lake project.")
    output.mkdir(parents=True, exist_ok=True)
    (output / "tmp").mkdir(exist_ok=True)
    os.environ["TMPDIR"] = str(output / "tmp")

    prefix = Path(subprocess.check_output(
        ["lean", "--print-prefix"], cwd=project, text=True).strip()).resolve()
    tools = {name: prefix / "bin" / name for name in
             ["lean", "lake", "leanexport", "leanchecker", "nanoda_bin", "con-ron"]}
    for name, executable in tools.items():
        if not executable.is_file() or not os.access(executable, os.X_OK):
            parser.error(f"The selected Lean toolchain does not provide executable {name}: {executable}")

    report = {
        "scope": "Selected compiled theorem/definition declarations and their transitive dependencies",
        "full_palomar_workflow": False,
        "independent_challenge_comparison": False,
        "sandbox_note": "Components run inside the surrounding execution sandbox; bwrap is not invoked.",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "project": str(project),
        "module": args.module,
        "declarations": args.declarations,
        "definition_targets": args.definition_target,
        "exported_declarations": exported_declarations,
        "proof_modules": list(dict.fromkeys([args.module, *args.proof_module])),
        "audited_definitions": args.definition,
        "permitted_axioms": AXIOMS,
        "toolchain_prefix": str(prefix),
        "tool_versions": {
            "lean": subprocess.check_output([str(tools["lean"]), "--version"], text=True).strip(),
            "lake": subprocess.check_output([str(tools["lake"]), "--version"], text=True).strip(),
        },
        "tool_sha256": {name: sha256(path) for name, path in tools.items()},
        "verifier_sha256": sha256(Path(__file__).resolve()),
        "input_sha256": {},
        "steps": [],
    }
    report_path = output / "results.json"
    if args.reuse_dependency_discovery and (
            project / args.reuse_dependency_discovery).resolve() == report_path:
        parser.error("Archive the previous results before reusing them; the current report is overwritten.")
    report["outcome"] = "verification-in-progress"
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    build_command = [str(tools["lake"]), "build", args.module]
    build_started = time.monotonic()
    print("Starting build", flush=True)
    with (output / "build.log").open("wb") as handle:
        build_result = subprocess.run(build_command, cwd=project, stdout=handle, stderr=handle)
    report["steps"].append({
        "label": "build", "command": build_command, "exit_code": build_result.returncode,
        "elapsed_seconds": round(time.monotonic() - build_started, 3),
        "log": str((output / "build.log").relative_to(project)), "stdout": None,
    })
    if build_result.returncode != 0:
        report["outcome"] = "build-failed"
        report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        return 1
    print("Finished build: exit 0", flush=True)
    if args.reuse_dependency_discovery:
        previous_path = (project / args.reuse_dependency_discovery).resolve()
        previous = json.loads(previous_path.read_text(encoding="utf-8"))
        if previous["module"] != args.module or previous["tool_sha256"] != report["tool_sha256"]:
            parser.error("Recorded dependency discovery uses a different module or toolchain.")
        local_modules = previous["local_dependency_closure"]
        pinned_inputs = ["lean-toolchain", "lake-manifest.json"]
        pinned_inputs.extend(name for name in ["lakefile.toml", "lakefile.lean"]
                             if name in previous["input_sha256"])
        pinned_inputs.extend(module.replace(".", "/") + ".lean" for module in local_modules)
        for relative in pinned_inputs:
            if sha256(project / relative) != previous["input_sha256"][relative]:
                parser.error(f"Cannot reuse dependency discovery: changed input {relative}")
        local_graph = previous["local_dependency_graph"]
        dependency_commands = previous["dependency_discovery"]
        report["dependency_discovery_reused_from"] = {
            "path": str(previous_path), "sha256": sha256(previous_path)}
        print("Reused Lean dependency discovery after checking every source and dependency-pin hash", flush=True)
    else:
        local_modules, local_graph, dependency_commands = local_dependency_closure(
            project, args.module, tools["lake"])
    report["local_dependency_closure"] = local_modules
    report["local_dependency_graph"] = local_graph
    report["dependency_discovery"] = dependency_commands
    if any(module not in local_modules for module in report["proof_modules"]):
        parser.error("Every --proof-module must belong to the selected module's local import closure.")
    input_paths = ["lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean"]
    for module in local_modules:
        module_path = module.replace(".", "/")
        input_paths.append(module_path + ".lean")
        input_paths.extend(".lake/build/lib/lean/" + module_path + suffix
                           for suffix in [".olean", ".olean.private", ".olean.server"])
    for relative in input_paths:
        path = project / relative
        if path.is_file():
            report["input_sha256"][relative] = sha256(path)

    def save() -> None:
        report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    def run(label: str, command: list[str], stdout_path: Path | None = None) -> int:
        log = output / (label + ".log")
        started = time.monotonic()
        print(f"Starting {label}", flush=True)
        if stdout_path is None:
            with log.open("wb") as handle:
                result = subprocess.run(command, cwd=project, stdout=handle, stderr=handle)
        else:
            with stdout_path.open("wb") as out, log.open("wb") as err:
                result = subprocess.run(command, cwd=project, stdout=out, stderr=err)
        report["steps"].append({
            "label": label,
            "command": command,
            "exit_code": result.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "log": str(log.relative_to(project)),
            "stdout": (str(stdout_path.relative_to(project)) if stdout_path.is_relative_to(project)
                       else str(stdout_path)) if stdout_path else None,
        })
        save()
        print(f"Finished {label}: exit {result.returncode}", flush=True)
        return result.returncode

    # The generated audit contains no proof declarations. It checks that each
    # target has its requested theorem/definition kind, prints its complete
    # type, and enforces the permitted-axiom list through Lean's own transitive
    # dependency traversal.
    lines = ["module", "public import Lean"]
    lines.extend(f"import all {module}" for module in report["proof_modules"])
    lines.extend([
        "",
        "open Lean", "set_option pp.universes true", "set_option pp.explicit true",
        "set_option format.width 120",
        "set_option pp.proofs false", "",
    ])
    for definition in args.definition:
        lines.extend([f"#print {definition}", ""])
    for declaration in args.declarations:
        lines.extend([f"#check @{declaration}", f"#print axioms {declaration}", ""])
    for declaration in args.definition_target:
        lines.extend([f"#check @{declaration}", f"#print axioms {declaration}", ""])
    quoted_names = ", ".join("``" + name for name in args.declarations)
    lines.extend([
        "run_cmd do",
        "  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]",
        "  let privateEnv := (← getEnv).setExporting false",
        f"  for name in #[{quoted_names}] do",
        "    match privateEnv.find? name with",
        "    | some (.thmInfo _) => pure ()",
        '    | _ => throwError "Selected declaration is not a theorem: {name}"',
        "    let axioms ← Lean.collectAxioms name",
        "    for axiomName in axioms do",
        "      unless permitted.contains axiomName do",
        '        throwError "Forbidden axiom {axiomName} in {name}"',
        '    logInfo m!"Axiom whitelist passed for {name}: {axioms}"',
    ])
    if args.definition_target:
        quoted_definitions = ", ".join("``" + name for name in args.definition_target)
        lines.extend([
            f"  for name in #[{quoted_definitions}] do",
            "    match privateEnv.find? name with",
            "    | some (.defnInfo _) => pure ()",
            '    | _ => throwError "Selected declaration is not a definition: {name}"',
            "    let axioms ← Lean.collectAxioms name",
            "    for axiomName in axioms do",
            "      unless permitted.contains axiomName do",
            '        throwError "Forbidden axiom {axiomName} in {name}"',
            '    logInfo m!"Definition axiom whitelist passed for {name}: {axioms}"',
        ])
    lines.append("")
    audit = output / "DeclarationAudit.lean"
    if audit in [project / (module.replace(".", "/") + ".lean") for module in local_modules]:
        parser.error("The generated audit path would overwrite a source file in the proof closure.")
    audit.write_text("\n".join(lines), encoding="utf-8")
    report["input_sha256"][str(audit.relative_to(project))] = sha256(audit)
    save()
    if run("declaration-audit", [
        str(tools["lake"]), "env", "lean", "-j", "1", "-R", str(project), str(audit),
    ]) != 0:
        report["outcome"] = "declaration-audit-failed"
        save()
        return 1
    report["imported_private_theorem_kinds_checked"] = True
    report["imported_private_definition_kinds_checked"] = bool(args.definition_target)

    export_path = (Path(args.export_file).expanduser().resolve()
                   if args.export_file else output / "selected.ndjson")
    if export_path.suffix != ".ndjson":
        parser.error("The export file must have the .ndjson suffix.")
    if export_path.exists():
        parser.error("Refusing to overwrite an existing export; choose a fresh --export-file/output directory.")
    export_path.parent.mkdir(parents=True, exist_ok=True)
    report["export_file"] = str(export_path)
    if run("export", [str(tools["lake"]), "env", "leanexport", args.module, "--",
                      *exported_declarations], export_path) != 0:
        report["outcome"] = "export-failed"
        save()
        return 1
    report["export_sha256"] = sha256(export_path)
    report["export_size_bytes"] = export_path.stat().st_size
    try:
        report["export_structure"] = inspect_export(export_path, args.declarations, args.definition_target)
    except (KeyError, ValueError, TypeError) as error:
        report["outcome"] = "export-structure-audit-failed"
        report["export_structure_error"] = str(error)
        save()
        print(str(error), file=sys.stderr)
        return 1
    save()

    nanoda_config = output / "nanoda.json"
    nanoda_config.write_text(json.dumps({
        "use_stdin": False,
        "export_file_path": str(export_path),
        "permitted_axioms": AXIOMS,
        "unpermitted_axiom_hard_error": True,
        "num_threads": 4,
        "nat_extension": True,
        "string_extension": True,
    }, indent=2) + "\n", encoding="utf-8")
    report["nanoda_unpermitted_axiom_hard_error"] = True
    report["nanoda_config_sha256"] = sha256(nanoda_config)
    statuses = [
        run("leanchecker", [str(tools["leanchecker"]), "--silent", "--from-export", str(export_path)]),
        run("nanoda", [str(tools["nanoda_bin"]), str(nanoda_config)]),
        run("con-ron", [str(tools["con-ron"]), "--jobs=4", str(export_path)]),
    ]
    components_accepted = all(status == 0 for status in statuses)
    changed = [relative for relative, digest in report["input_sha256"].items()
               if not (project / relative).is_file() or sha256(project / relative) != digest]
    report["export_unchanged_during_kernel_checks"] = sha256(export_path) == report["export_sha256"]
    if not report["export_unchanged_during_kernel_checks"]:
        changed.append(str(export_path))
    report["changed_inputs_during_verification"] = changed
    changed_proof_inputs = [name for name in changed if name not in ["lakefile.toml", "lakefile.lean"]]
    report["proof_inputs_unchanged"] = not changed_proof_inputs
    report["component_outcome"] = "all-components-accepted" if components_accepted else "one-or-more-components-unsuccessful"
    accepted = components_accepted and not changed_proof_inputs
    if not components_accepted:
        report["outcome"] = "one-or-more-components-unsuccessful"
    elif changed_proof_inputs:
        report["outcome"] = "all-components-accepted-but-proof-inputs-changed"
    elif changed:
        report["outcome"] = "all-components-accepted-with-configuration-drift"
    else:
        report["outcome"] = "all-components-accepted"
    report["driver_exit_code"] = 0 if accepted else 1
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    save()
    print(report["outcome"], flush=True)
    return 0 if accepted else 1


if __name__ == "__main__":
    sys.exit(main())
