#!/usr/bin/env python3
"""Check v1.8 correspondence, explicitly retaining both earlier source versions.

Hashes and compiled types establish identity, not semantic equivalence. The
changed statements require a separately recorded comparison of their hypotheses,
objects and quantifiers with the actual compiled proof endpoints.
"""

from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys

import check_sources
from check_revised_sources import PATTERN

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "manuscripts/paper-p1/v1.8"
SOURCE = PACKAGE / "sources"
LEDGER = ROOT / "docs/manuscript-results-v1.8.json"
REVISION = ROOT / "docs/manuscript-v1.8-revision.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative_file(value):
    path = ROOT / value
    if not path.resolve().is_relative_to(ROOT.resolve()):
        raise ValueError(f"Path escapes the repository: {value}")
    return path


def included_sources(document):
    """Resolve literal inputs from the actual TeX working directory."""
    pending = [SOURCE / f"{document}.tex"]
    visited = set()
    while pending:
        path = pending.pop()
        if path in visited:
            continue
        if not path.resolve().is_relative_to(SOURCE.resolve()):
            raise ValueError(f"TeX input escapes the source directory: {path}")
        text = path.read_text()
        visited.add(path)
        text = re.sub(r"(?<!\\)%[^\n]*", "", text)
        for value in re.findall(r"\\input\{([^}]+)\}", text):
            if "\\" in value or "#" in value:
                raise ValueError(f"Unresolved dynamic TeX input: {value}")
            child = SOURCE / value
            if child.suffix != ".tex":
                child = child.with_suffix(".tex")
            pending.append(child)
    return visited


def statements():
    records = {}
    included = {doc: included_sources(doc) for doc in ("main", "companion")}
    for document in included:
        for path in sorted((SOURCE / f"{document}_sections").rglob("*.tex")):
            text = path.read_text()
            for match in PATTERN.finditer(text):
                if path not in included[document]:
                    raise ValueError(f"Numbered result is not included in {document}: {path}")
                if path in included["companion" if document == "main" else "main"]:
                    raise ValueError(f"Numbered result is included in both documents: {path}")
                label = re.search(r"\\label\{([^}]+)\}", match.group(0))
                if label is None or label[1] in records:
                    raise ValueError(f"Missing or duplicate numbered-result label: {path}")
                records[label[1]] = {
                    "document": document,
                    "source": str(path.relative_to(SOURCE)),
                    "line": text[:match.start()].count("\n") + 1,
                    "sha256": hashlib.sha256(match.group(0).encode()).hexdigest(),
                }
    # Shared files must not conceal new numbered results outside the inventory.
    section_sources = set(SOURCE.glob("main_sections/**/*.tex")) | set(
        SOURCE.glob("companion_sections/**/*.tex"))
    for path in set.union(*included.values()) - section_sources:
        if PATTERN.search(path.read_text()):
            raise ValueError(f"Uninventoried numbered statement in shared TeX: {path}")
    return records


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-proved", action="store_true")
    args = parser.parse_args()
    subprocess.run([sys.executable, str(ROOT / "scripts/check_revised_sources.py"),
                    "--require-proved"], check=True)
    check_sources.check_manifest(SOURCE)
    files = {str(p.relative_to(SOURCE)): sha(p) for p in SOURCE.rglob("*.tex")
             if "build" not in p.relative_to(SOURCE).parts}
    manifest = [line.split(maxsplit=1)[1].lstrip("*")
                for line in (SOURCE / "MANIFEST_SHA256.txt").read_text().splitlines()
                if line.strip()]
    if len(manifest) != len(files) or set(manifest) != set(files):
        raise ValueError("The v1.8 manifest does not cover exactly its authored TeX sources")
    provenance = json.loads((PACKAGE / "PROVENANCE.json").read_text())
    if provenance["files"] != [{"path": p, "sha256": files[p]} for p in sorted(files)]:
        raise ValueError("The v1.8 provenance differs from the current source hashes")
    previous = {row["label"]: row for row in json.loads(
        (ROOT / "docs/manuscript-results-v1.7.json").read_text())["results"]}
    original = {row["label"]: row for row in json.loads(
        (ROOT / "docs/manuscript-results.json").read_text())["results"]}
    actual = statements()
    ledger = json.loads(LEDGER.read_text())
    rows = ledger["results"]
    if (len(rows) != 167 or len(actual) != 167 or set(actual) != set(previous)
            or {row["label"] for row in rows} != set(previous)):
        raise ValueError("The 167 original numbered-result identities must be preserved")
    revision = json.loads(REVISION.read_text())
    proof_path = relative_file(revision["proof_source_manifest"]["path"])
    if sha(proof_path) != revision["proof_source_manifest"]["sha256"]:
        raise ValueError("Proof-source manifest checksum mismatch")
    proof_sources = json.loads(proof_path.read_text())["files"]
    actual_proofs = set((ROOT / "PaperP1").rglob("*.lean")) | set(ROOT.glob("*.lean"))
    actual_proofs.update(ROOT / p for p in ["lean-toolchain", "lake-manifest.json"])
    expected_proofs = {str(p.relative_to(ROOT)): sha(p) for p in actual_proofs}
    if proof_sources != [{"path": p, "sha256": expected_proofs[p]}
                         for p in sorted(expected_proofs)]:
        raise ValueError("Proof sources or compiler/dependency pins changed since their validation")
    changed = {label for label in actual if actual[label]["sha256"] != previous[label]["sha256"]}
    changes = revision["numbered_statement_changes"]
    if len(changes) != len({row["label"] for row in changes}) or {
            row["label"] for row in changes} != changed:
        raise ValueError("The revision record must identify every changed statement once")
    type_path = relative_file(revision["compiled_types"]["path"])
    if sha(type_path) != revision["compiled_types"]["sha256"]:
        raise ValueError("Compiled type report checksum mismatch")
    if revision["compiled_types"]["actual_exit_code"] != 0:
        raise ValueError("The compiled type extraction did not succeed")
    types = {row["name"]: row for row in json.loads(type_path.read_text())}
    audit_names = set(json.loads((ROOT / "docs/axiom-audit-declarations.json").read_text()))
    by_label = {row["label"]: row for row in changes}
    for row in rows:
        label = row["label"]
        for key, value in actual[label].items():
            if row[key] != value:
                raise ValueError(f"Current source locator/hash mismatch: {label}, {key}")
        if (row["baseline_sha256"] != original[label]["sha256"]
                or row["previous_sha256"] != previous[label]["sha256"]
                or row["source_changed"] != (row["sha256"] != original[label]["sha256"])):
            raise ValueError(f"Original or previous source identity lost: {label}")
        if row["status"] not in {"proved", "pending_alignment", "pending_validation"}:
            raise ValueError(f"Invalid v1.8 result status: {label}")
        if args.require_proved and row["status"] != "proved":
            raise ValueError(f"Unfinished statement comparison: {label}")
        if not row["lean_declarations"]:
            raise ValueError(f"Missing proof references: {label}")
        if label in changed:
            change = by_label[label]
            if (change["previous_sha256"] != row["previous_sha256"]
                    or change["sha256"] != row["sha256"]):
                raise ValueError(f"Revision statement hashes differ: {label}")
            if args.require_proved and change["semantic_alignment"]["status"] != "passed":
                raise ValueError(f"Semantic comparison is not complete: {label}")
            if not all(change["semantic_alignment"].get(key)
                       for key in ["objects", "hypotheses", "quantifiers"]):
                raise ValueError(f"Missing explicit semantic comparison: {label}")
            endpoints = [row["canonical_statement"]] + row.get("canonical_additional_statements", [])
            if (not endpoints or endpoints != change["proof_endpoints"]
                    or not set(endpoints) <= set(row["lean_declarations"])):
                raise ValueError(f"Missing explicit proof endpoint correspondence: {label}")
            for name in endpoints:
                compiled = types.get(name, {})
                if (name not in audit_names or compiled.get("kind") != "theorem"
                        or compiled.get("is_proposition") is not True):
                    raise ValueError(f"Endpoint is not an audited compiled theorem: {name}")
                digest = hashlib.sha256(compiled["type"].encode()).hexdigest()
                if change["proof_type_sha256"].get(name) != digest:
                    raise ValueError(f"Compiled endpoint type differs from its comparison: {name}")
            if row["remaining_unformalized_inputs"]:
                raise ValueError(f"A strengthened statement retains an unformalized input: {label}")
        else:
            for key in ["lean_declarations", "canonical_statement", "canonical_additional_statements",
                        "remaining_unformalized_inputs"]:
                if row.get(key) != previous[label].get(key):
                    raise ValueError(f"Unchanged statement lost its previous proof correspondence: {label}")
    draft_map = json.loads((PACKAGE / "CHANGE_MAP.json").read_text())
    expected_aux = {row["id"]: row for row in draft_map["unnumbered_scientific_statements"]}
    auxiliary = revision["unnumbered_statement_correspondence"]
    if len(auxiliary) != len(expected_aux) or {row["id"] for row in auxiliary} != set(expected_aux):
        raise ValueError("Every unnumbered scientific claim must have its own correspondence")
    for row in auxiliary:
        expected = expected_aux[row["id"]]
        path = SOURCE / row["source"]
        if (not path.resolve().is_relative_to(SOURCE.resolve())
                or row["source"] != expected["location"]["file"]
                or row["line"] != expected["location"]["line"]
                or sha(path) != row["source_sha256"]):
            raise ValueError(f"Auxiliary source locator/hash mismatch: {row['id']}")
        if not row["hypotheses_and_quantifiers"] or not row["proof_endpoints"]:
            raise ValueError(f"Missing auxiliary hypotheses or proof endpoints: {row['id']}")
        if args.require_proved and row["semantic_alignment_status"] != "passed":
            raise ValueError(f"Unfinished auxiliary comparison: {row['id']}")
        for name in row["proof_endpoints"]:
            compiled = types.get(name, {})
            if (name not in audit_names or compiled.get("kind") != "theorem"
                    or compiled.get("is_proposition") is not True):
                raise ValueError(f"Auxiliary endpoint is not an audited theorem: {name}")
            if row["proof_type_sha256"].get(name) != hashlib.sha256(compiled["type"].encode()).hexdigest():
                raise ValueError(f"Auxiliary compiled type mismatch: {name}")
    print(f"Verified {len(files)} v1.8 source hashes and all 167 numbered results.")
    print(f"Explicit comparisons: {len(changed)} strengthened/reworded statements; "
          f"{sum(row['status'] == 'proved' for row in rows)}/167 proved.")
    print(f"All {len(auxiliary)} unnumbered scientific claims have source-bound compiled proof correspondence.")
    print("Both earlier manuscript versions and the two false-original statuses are preserved.")
    print("Scope: source identity and recorded correspondence; hashes alone are not a semantic proof.")


if __name__ == "__main__":
    main()
