#!/usr/bin/env python3
"""Verify preserved source bytes and the 167-result inventory, not proofs."""

import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "manuscripts/paper-p1/v1.6"
SOURCE = PACKAGE / "sources"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest(directory):
    entries = 0
    for row in (directory / "MANIFEST_SHA256.txt").read_text().splitlines():
        if not row.strip():
            continue
        digest, name = row.split(maxsplit=1)
        path = directory / name.lstrip("*")
        if not path.resolve().is_relative_to(directory.resolve()):
            raise ValueError(f"Manifest path escapes directory: {name}")
        if sha(path) != digest:
            raise ValueError(f"Source identity mismatch: {path}")
        entries += 1
    return entries


def main():
    counts = [check_manifest(PACKAGE), check_manifest(SOURCE)]
    provenance = json.loads((PACKAGE / "PROVENANCE.json").read_text())
    for record in provenance["files"]:
        path = PACKAGE / record["path"]
        if sha(path) != record["sha256"]:
            raise ValueError(f"Provenance mismatch: {path}")
    baseline = json.loads((SOURCE / "editorial/v15_statement_baseline.json").read_text())
    pattern = re.compile(r"\\begin\{(theorem|proposition|lemma|corollary)\}.*?\\end\{\1\}", re.S)
    statements = {}
    for document in ("main", "companion"):
        for path in (SOURCE / f"{document}_sections").glob("*.tex"):
            for match in pattern.finditer(path.read_text()):
                block = match.group(0)
                label = re.search(r"\\label\{([^}]+)\}", block).group(1)
                if label in statements:
                    raise ValueError(f"Duplicate statement: {label}")
                statements[label] = {
                    "sha256": hashlib.sha256(block.encode()).hexdigest(),
                    "document": document,
                    "source": str(path.relative_to(SOURCE)),
                    "line": path.read_text()[:match.start()].count("\n") + 1,
                }
    if len(statements) != 167 or statements.keys() != baseline.keys():
        raise ValueError("The 167-statement baseline is not preserved")
    ledger = json.loads((ROOT / "docs/manuscript-results.json").read_text())
    entries = ledger["results"]
    if len(entries) != 167 or {r["label"] for r in entries} != statements.keys():
        raise ValueError("The coverage ledger does not match the source labels")
    allowed = {"not_started", "in_progress", "proved", "conditional", "blocked"}
    for entry in entries:
        label = entry["label"]
        original = statements[label]
        if original["sha256"] != baseline[label]["sha256"]:
            raise ValueError(f"Original statement changed: {label}")
        for key in ("sha256", "document", "source", "line"):
            if entry[key] != original[key]:
                raise ValueError(f"Coverage locator mismatch: {label}, {key}")
        if entry["status"] not in allowed:
            raise ValueError(f"Unknown status: {label}")
        if entry["status"] in {"proved", "conditional"} and not entry["lean_declarations"]:
            raise ValueError(f"Completed status without declarations: {label}")
    expected_toolchain = "leanprover/lean4:v4.36.0-rc2"
    if (ROOT / "lean-toolchain").read_text().strip() != expected_toolchain:
        raise ValueError("Unexpected Lean toolchain")
    lock = ROOT / "lake-manifest.json"
    if lock.exists():
        mathlib = next(p for p in json.loads(lock.read_text())["packages"] if p["name"] == "mathlib")
        if mathlib["rev"] != "9d581dfff2e41de989072ea63abf3daf69311520":
            raise ValueError("Unexpected Mathlib lock revision")
    print(f"Verified {sum(counts)} manifest entries and {len(entries)} numbered results.")
    print("Scope: source integrity and inventory only, not mathematical proof certification.")


if __name__ == "__main__":
    main()
