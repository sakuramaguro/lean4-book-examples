#!/usr/bin/env python3
"""Validate the complete Volume 4 source inventory without requiring a manuscript."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re

ROOT = Path(__file__).resolve().parents[1]
CATALOG = ROOT / "catalog/reader.json"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DIAGNOSTIC_PATTERN = r"\b(?:error|warning)(?:\([^\n]*?\))?:"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def from_author(data):
    """Export only source identities, proof categories and declaration locations."""
    return dict(schema_version=1, profile="volume4", lean_inputs=dict(sorted(data["lean_inputs"].items())),
                blocks=[{key: row[key] for key in ("id", "file", "sha256", "purpose", "names")}
                        for row in data["blocks"]],
                declarations=[{key: row[key] for key in ("name", "file", "line")}
                              for row in data["declarations"]])


def source_inputs():
    result = {}
    for folder, dirs, names in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in {".lake", ".generated", "__pycache__", "reader-template"}]
        for name in names:
            path = Path(folder) / name
            if path.suffix == ".lean" or path.parent == ROOT and name in {
                "lean-toolchain", "lakefile.toml", "lake-manifest.json"
            }:
                require(not path.is_symlink(), f"Source symlink: {path.name}")
                result[path.relative_to(ROOT).as_posix()] = digest(path.read_bytes())
    return result


def check_diagnostics(output):
    require(not re.search(DIAGNOSTIC_PATTERN, output) and "sorryAx" not in output,
            "Unexpected diagnostic or sorryAx")


def parse_axioms(output, expected):
    dependencies = {}
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, output):
        name, raw = match.groups()
        require(name not in dependencies, f"Duplicate audit output: {name}")
        values = [x.strip() for x in (raw or "").split(",") if x.strip()]
        require(not (set(values) - ALLOWED_AXIOMS), f"Unreviewed axioms: {name}: {values}")
        dependencies[name] = values
    require(set(dependencies) == set(expected) and len(expected) == len(set(expected)),
            "Missing, duplicate or extra audit target")
    return dependencies


def validate(data=None):
    data = json.loads(CATALOG.read_text()) if data is None else data
    require(set(data) == {"schema_version", "profile", "lean_inputs", "blocks", "declarations"}
            and data["schema_version"] == 1 and data["profile"] == "volume4", "Invalid reader catalog")
    for name, hash_value in data["lean_inputs"].items():
        path = PurePosixPath(name)
        require(not path.is_absolute() and ".." not in path.parts and str(path) == name,
                "Invalid source path")
        require(re.fullmatch(r"[0-9a-f]{64}", hash_value) is not None, "Invalid source hash")
    require(source_inputs() == data["lean_inputs"] and len(data["lean_inputs"]) == 110,
            "Lean inputs changed or missing; review the source inventory")
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.0-rc1",
            "Wrong Volume 4 toolchain")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = manifest["packages"]
    require(manifest["packagesDir"] == ".lake/packages" and len(packages) == 13
            and len({p["name"] for p in packages}) == 13, "Incomplete fixed dependencies")
    require(all(p["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", p["rev"])
                for p in packages), "Unpinned dependency")
    rows = data["blocks"]
    by_id = {r["id"]: r for r in rows}
    require(len(rows) == len(by_id) == len({r["file"] for r in rows}) == 89,
            "Missing or duplicate reader block")
    require(sum(r["purpose"] == "completed_proof" for r in rows) == 83
            and sum(r["purpose"] == "statement_inspection" for r in rows) == 6,
            "Reader proof/inspection classification differs")
    for row in rows:
        require(set(row) == {"id", "file", "sha256", "purpose", "names"}, "Invalid reader block fields")
        require(row["file"] in data["lean_inputs"], "Block file missing from source inventory")
        code = (ROOT / row["file"]).read_text()
        require(digest(code.encode()) == row["sha256"] and code.startswith("import "),
                f'{row["id"]}: code/source mismatch')
        require(bool(row["names"]) == (row["purpose"] == "completed_proof"),
                "Reader declaration purpose mismatch")
    declarations = data["declarations"]
    names = [d["name"] for d in declarations]
    require(len(names) == len(set(names)) == 212, "Missing or duplicate audit declaration")
    for declaration in declarations:
        require(set(declaration) == {"name", "file", "line"}
                and declaration["file"] in data["lean_inputs"], "Invalid declaration source")
        require(type(declaration["line"]) is int and declaration["line"] > 0,
                "Invalid declaration line")
        line = (ROOT / declaration["file"]).read_text().splitlines()[declaration["line"] - 1]
        require(re.search(r"\btheorem\s+(?:\w+\.)*" + re.escape(declaration["name"].split(".")[-1]) + r"\b", line),
                f'{declaration["name"]}: declaration moved or changed')
    printed = re.findall(r"^#print axioms ([\w.]+)$", (ROOT / "Audit.lean").read_text(), re.M)
    require(len(printed) == len(set(printed)) and set(printed) == set(names), "Incomplete Audit.lean coverage")
    for row in rows:
        expected = {d["name"] for d in declarations if d["file"] == row["file"]}
        require(set(row["names"]) == expected and len(row["names"]) == len(expected),
                f'{row["id"]}: declaration inventory differs')
    for name in data["lean_inputs"]:
        if name.endswith(".lean"):
            require(not re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", (ROOT / name).read_text()),
                    f"{name}: unfinished or unchecked declaration")
    return data, by_id, dict(matched_code_blocks=89, completed_proof_blocks=83,
                            statement_inspection_blocks=6, audited_declarations=212, lean_inputs=110)


if __name__ == "__main__":
    try:
        _, _, counts = validate()
        print(json.dumps(dict(status="passed", **counts), indent=2))
    except (ValueError, OSError, KeyError, IndexError, TypeError) as error:
        raise SystemExit(f"FAILED: {error}")
