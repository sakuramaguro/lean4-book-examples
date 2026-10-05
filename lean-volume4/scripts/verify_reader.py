#!/usr/bin/env python3
"""Verify Volume 4 in its own pinned Lake environment, retaining no stale success."""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
import os
import re
import signal
import subprocess
import sys

import reader_catalog
from reader_catalog import check_diagnostics, parse_axioms

ROOT = reader_catalog.ROOT
OUTPUT = ROOT / ".generated"
LOGS = OUTPUT / "logs"


def run(args, logfile, cwd=ROOT):
    process = subprocess.Popen(args, cwd=cwd, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        output, _ = process.communicate(timeout=900)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        output, _ = process.communicate()
        (LOGS / logfile).write_text(output)
        raise RuntimeError(f"Timed out; see .generated/logs/{logfile}")
    (LOGS / logfile).write_text(output)
    if process.returncode:
        raise RuntimeError(f"Exit {process.returncode}; see .generated/logs/{logfile}")
    return output


def verify(validator, test_script, result_name, scope):
    LOGS.mkdir(parents=True, exist_ok=True)
    result_file = OUTPUT / result_name
    result_file.unlink(missing_ok=True)
    if os.environ.get("LEAN_PATH"):
        raise ValueError("Run without a manually configured LEAN_PATH")
    run([sys.executable, test_script], "validation-tests.log")
    data, actual, counts = validator()
    print(f"Catalog: {len(actual)} blocks, {counts['audited_declarations']} declarations.", flush=True)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    dependencies = {}
    for package in manifest["packages"]:
        reader_catalog.require(package["type"] == "git", "Unreviewed non-git dependency")
        path = ROOT / manifest["packagesDir"] / package["name"]
        revision = run(["git", "rev-parse", "HEAD"], f'dep-{package["name"]}-rev.log', path).strip()
        changes = run(["git", "status", "--porcelain", "--untracked-files=no"],
                      f'dep-{package["name"]}-status.log', path).strip()
        reader_catalog.require(revision == package["rev"] and not changes,
                        f'Dependency differs: {package["name"]}')
        dependencies[package["name"]] = revision
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    version = run(["lake", "env", "lean", "--version"], "version.log").strip()
    reader_catalog.require(version.startswith("Lean (version " + toolchain.rsplit(":v", 1)[-1] + ","),
                    f"Wrong Lean version: {version}")
    print(f"Pinned environment: {len(dependencies)} packages. Building...", flush=True)
    check_diagnostics(run(["lake", "build"], "build.log"))
    output = run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "Audit.lean"],
                 "axioms.log")
    check_diagnostics(output)
    axioms = parse_axioms(output, [d["name"] for d in data["declarations"]])
    print(f"Build and {len(axioms)} declaration audits passed. Checking independent files...", flush=True)

    def check(row):
        output = run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", row["file"]],
                     row["id"] + ".log")
        check_diagnostics(output)
        return dict(id=row["id"], purpose=row["purpose"], file=row["file"],
                    source_sha256=actual[row["id"]]["sha256"], exit_code=0)

    with ThreadPoolExecutor(max_workers=2) as pool:
        checks = list(pool.map(check, data["blocks"]))
    final_data, _, _ = validator()
    reader_catalog.require(final_data == data, "Catalog changed during verification")
    reader_catalog.require(len(checks) == len(actual) and {c["id"] for c in checks} == set(actual),
                    "Independent execution coverage mismatch")
    result = dict(status="passed", checked_at=datetime.now(timezone.utc).isoformat(),
                  toolchain=toolchain, lean_version=version, dependencies=dependencies,
                  lean_inputs=data["lean_inputs"], coverage=counts,
                  normal_lake_build=True, manual_LEAN_PATH_override=False,
                  audited_declarations=axioms, independent_checks=checks,
                  scope=scope)
    for key in ("source_files", "config_sha256"):
        if key in data:
            result[key] = data[key]
    result_file.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(f"Full verification passed: 83 proofs, 6 inspections, 212 declarations.", flush=True)


def main():
    verify(reader_catalog.validate, "scripts/test_reader_validation.py", "reader-verification.json",
           "Pinned reader sources, dependencies, build, 89 examples and 212 axiom audits. "
           "Does not verify manuscript prose, browser layout, publication or untested operating systems.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, RuntimeError, KeyError, IndexError) as error:
        print(f"FAILED: {error}", file=sys.stderr)
        sys.exit(1)
