#!/usr/bin/env python3
"""Check the separate v1.7 source inventory and its explicit proof correspondence."""

from pathlib import Path
import argparse
import hashlib
import json
import re

import check_sources

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "manuscripts/paper-p1/v1.7"
SOURCE = PACKAGE / "sources"
LEDGER = ROOT / "docs/manuscript-results-v1.7.json"
CORRECTED = {"p1:arith:asymmetric", "p13:short:quadratic"}
PATTERN = re.compile(r"\\begin\{(theorem|proposition|lemma|corollary)\}.*?\\end\{\1\}", re.S)


def statements():
    records = {}
    for document in ["main", "companion"]:
        for path in sorted((SOURCE / f"{document}_sections").glob("*.tex")):
            text = path.read_text()
            for match in PATTERN.finditer(text):
                label_match = re.search(r"\\label\{([^}]+)\}", match.group(0))
                if not label_match:
                    raise ValueError(f"Unlabelled numbered statement: {path}")
                label = label_match.group(1)
                if label in records:
                    raise ValueError(f"Duplicate revised statement: {label}")
                records[label] = {
                    "document": document,
                    "source": str(path.relative_to(SOURCE)),
                    "line": text[:match.start()].count("\n") + 1,
                    "sha256": hashlib.sha256(match.group(0).encode()).hexdigest(),
                }
    return records


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-proved", action="store_true")
    args = parser.parse_args()
    check_sources.main()
    count = check_sources.check_manifest(SOURCE)
    actual_sources = {
        str(path.relative_to(SOURCE))
        for path in SOURCE.rglob("*.tex")
        if "build" not in path.relative_to(SOURCE).parts
    }
    manifest_sources = [
        line.split(maxsplit=1)[1].lstrip("*")
        for line in (SOURCE / "MANIFEST_SHA256.txt").read_text().splitlines()
        if line.strip()
    ]
    if len(manifest_sources) != len(actual_sources) or set(manifest_sources) != actual_sources:
        raise ValueError("Revised manifest does not cover exactly the authored TeX sources")
    baseline = json.loads((ROOT / "docs/manuscript-results.json").read_text())["results"]
    old = {row["label"]: row for row in baseline}
    current = statements()
    if len(current) != 167 or set(current) != set(old):
        raise ValueError("The revised source does not have the same 167 labelled statements")
    changed = {label for label in current if current[label]["sha256"] != old[label]["sha256"]}
    if changed != CORRECTED:
        raise ValueError(f"Unexpected revised statement changes: {sorted(changed)}")
    ledger = json.loads(LEDGER.read_text())
    revised = ledger["results"]
    if len(revised) != 167 or {row["label"] for row in revised} != set(old):
        raise ValueError("The revised proof ledger has the wrong inventory")
    known = {
        name
        for row in baseline
        for name in row.get("lean_declarations", [])
    }
    for finding in json.loads((ROOT / "docs/mathematical-changes.json").read_text())["findings"]:
        known.update(finding.get("evidence", []))
    for row in revised:
        label = row["label"]
        for key in ["document", "source", "line", "sha256"]:
            if row[key] != current[label][key]:
                raise ValueError(f"Revised source locator mismatch: {label}, {key}")
        if row["baseline_sha256"] != old[label]["sha256"]:
            raise ValueError(f"Original source identity lost: {label}")
        if row["source_changed"] != (label in CORRECTED):
            raise ValueError(f"Incorrect revision scope: {label}")
        if row["status"] not in {"proved", "pending_validation"}:
            raise ValueError(f"Unexpected revised validation status: {label}")
        if args.require_proved and row["status"] != "proved":
            raise ValueError(f"Revised statement still awaits validation: {label}")
        if not row["lean_declarations"] or not set(row["lean_declarations"]) <= known:
            raise ValueError(f"Unrecorded revised proof reference: {label}")
        if row.get("canonical_statement") and row["canonical_statement"] not in row["lean_declarations"]:
            raise ValueError(f"Canonical declaration is outside revised evidence: {label}")
        if label not in CORRECTED and old[label]["status"] != "proved":
            raise ValueError(f"Unchanged original statement is not proved: {label}")
    for label in CORRECTED:
        if old[label]["status"] != "in_progress":
            raise ValueError("A false original was silently relabelled as proved")
    provenance = json.loads((PACKAGE / "PROVENANCE.json").read_text())
    if {row["path"] for row in provenance["files"]} != actual_sources:
        raise ValueError("Revised source provenance has an incomplete inventory")
    for row in provenance["files"]:
        path = SOURCE / row["path"]
        if not path.resolve().is_relative_to(SOURCE.resolve()):
            raise ValueError("Revised provenance path escapes its source directory")
        if check_sources.sha(path) != row["sha256"]:
            raise ValueError(f"Revised source provenance mismatch: {row['path']}")
    proved = sum(row["status"] == "proved" for row in revised)
    print(f"Verified {count} revised TeX source hashes and 167 revised statements.")
    print(f"Exactly two original statements corrected; revised proofs: {proved}/167.")
    print("Original v1.6 identities and false-original statuses remain preserved.")


if __name__ == "__main__":
    main()
