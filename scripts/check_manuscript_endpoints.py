#!/usr/bin/env python3
"""Check the source/type bindings of the complete v1.8 proof-entry index.

This verifies identities and the recorded scope review. It does not turn a
hash comparison into a machine translation of a TeX mathematical statement.
"""

from collections import Counter
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

from check_revised_sources_v18 import statements
from update_audit import declaration_names, lean_code

ROOT = Path(__file__).resolve().parents[1]
INDEX = ROOT / "docs/manuscript-endpoints-v1.8.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local_file(value):
    path = ROOT / value
    if not path.resolve().is_relative_to(ROOT.resolve()):
        raise ValueError(f"Index path escapes the repository: {value}")
    return path


def source_locations():
    result = {}
    for path in sorted((ROOT / "PaperP1").rglob("*.lean")):
        names = declaration_names(path)
        code = lean_code(path.read_text())
        matches = list(re.finditer(
            r"^(?:@\[[^\n]*\][ \t]*)*(?:theorem|lemma) ([A-Za-z0-9_.']+)(?=\s|\[|\{)",
            code, re.M))
        if len(names) != len(matches):
            raise ValueError(f"Cannot match every declaration in {path}")
        digest = sha(path)
        for name, match in zip(names, matches, strict=True):
            result[name] = {"source": str(path.relative_to(ROOT)),
                            "line": code[:match.start()].count("\n") + 1,
                            "source_sha256": digest}
    return result


def verify(index, *, compiled=None, locations=None):
    actual = statements()
    ledger_path = ROOT / "docs/manuscript-results-v1.8.json"
    ledger = {r["label"]: r for r in json.loads(ledger_path.read_text())["results"]}
    if (index["source_ledger"]["path"] != "docs/manuscript-results-v1.8.json"
            or index["source_ledger"]["sha256"] != sha(ledger_path)):
        raise ValueError("The manuscript-result ledger changed")
    rows = index["results"]
    if (len(rows) != 167 or len({r["label"] for r in rows}) != 167
            or {r["label"] for r in rows} != set(actual)):
        raise ValueError("The proof-entry index must cover every one of the 167 labels once")
    if Counter(r["document"] for r in rows) != {"main": 73, "companion": 94}:
        raise ValueError("The article/companion partition changed")
    type_path = local_file(index["compiled_scope"]["path"])
    if sha(type_path) != index["compiled_scope"]["sha256"]:
        raise ValueError("Compiled proof-entry types changed")
    validation_path = local_file(index["compiled_scope"]["validation"])
    validation = json.loads(validation_path.read_text())
    scope_dir = type_path.parent
    if (validation["actual_exit_code"] != 0
            or validation["all_propositions_standard_axioms_only"] is not True
            or validation["compiled_types_sha256"] != sha(type_path)
            or (scope_dir / "compiled-types.exit").read_text().strip() != "0"
            or validation["log_sha256"] != sha(scope_dir / "compiled-types.log")
            or validation["inventory_sha256"] != sha(scope_dir.parent / "scope-declarations.json")):
        raise ValueError("The actual compiled scope replay did not pass")
    if compiled is None:
        compiled = {r["name"]: r for r in json.loads(type_path.read_text())}
    if locations is None:
        locations = source_locations()
    audit = set(json.loads((ROOT / "docs/axiom-audit-declarations.json").read_text()))
    revision = json.loads((ROOT / "docs/manuscript-v1.8-revision.json").read_text())
    proof_manifest = revision["proof_source_manifest"]
    if index["proof_source_manifest"] != proof_manifest:
        raise ValueError("The index and manuscript comparison use different proof snapshots")
    if index["proof_source_commit"] != revision["proof_source_commit"]:
        raise ValueError("The index proof-source commit is stale")
    replay = json.loads(local_file(index["proof_validation"]).read_text())
    if (replay["source_commit"] != index["proof_source_commit"]
            or replay["status"] != "passed"
            or replay["actual_process_exit_codes"] != {"build": 0, "audit": 0, "references": 0}
            or replay["compiled_scope"]["actual_exit_code"] != 0
            or replay["compiled_scope"]["replay_source_commit"] != index["proof_source_commit"]):
        raise ValueError("The index is not bound to a successful complete proof replay")
    for log in replay["logs"]:
        if sha(local_file(log["path"])) != log["sha256_gzip"]:
            raise ValueError(f"Complete proof replay log changed: {log['kind']}")
    for record in index["review_records"]:
        if sha(local_file(record["path"])) != record["sha256"]:
            raise ValueError(f"Frozen review record changed: {record['path']}")
    review_root = ROOT / "docs/reviews/2026-11-07"
    canonical = {r["label"]: r for r in json.loads(
        (review_root / "endpoint-canonical.json").read_text())["results"]}
    dense = {r["label"]: r for r in json.loads(
        (review_root / "endpoint-dense.json").read_text())["results"]}
    parent = json.loads((review_root / "endpoint-parent.json").read_text())["notes"]
    actual_partition = Counter(r["scope_review"]["source"] for r in rows)
    if (set(canonical) & set(dense)
            or index["review_partition"] != {
                "independent_canonical": len(canonical),
                "independent_dense": len(dense), "parent": len(parent)}
            or actual_partition != {"independent-canonical": 79, "independent-dense": 9,
                                    "parent-source-type-definition-comparison": 79}):
        raise ValueError("The recorded 79/9/79 review partition changed")
    changes = json.loads((ROOT / "docs/mathematical-changes.json").read_text())["findings"]
    extensions = {}
    for change in changes:
        if change["id"] in index["subsequent_exact_interfaces"]:
            if change["validation"]["status"] != "passed":
                raise ValueError(f"An additional interface is not validated: {change['id']}")
            extensions.setdefault(change["location"]["label"], set()).update(change["evidence"])
    distinct = set()
    for row in rows:
        label = row["label"]
        original = ledger[label]
        source = row["source"]
        expected_source = "manuscripts/paper-p1/v1.8/sources/" + actual[label]["source"]
        if (row["number"] != original["number"] or row["document"] != original["document"]
                or row["title"] != original["title"] or source["path"] != expected_source
                or source["line"] != actual[label]["line"]
                or source["statement_sha256"] != actual[label]["sha256"]
                or source["file_sha256"] != sha(local_file(source["path"]))
                or hashlib.sha256(source["statement"].encode()).hexdigest() != actual[label]["sha256"]
                or source["statement"] not in local_file(source["path"]).read_text()):
            raise ValueError(f"Source identity or locator mismatch: {label}")
        entries = row["entry_points"]
        if not entries or len({r["name"] for r in entries}) != len(entries):
            raise ValueError(f"Missing or duplicate proof entry: {label}")
        review = row["scope_review"]
        if (review["status"] != "source_type_and_definition_reviewed"
                or not review["notes"] or not review["inherited_hypotheses"]):
            raise ValueError(f"Incomplete recorded scope review: {label}")
        selected = {r["name"] for r in entries}
        allowed = set(original["lean_declarations"]) | extensions.get(label, set())
        if label in canonical:
            recorded = canonical[label]
            required = {recorded["canonical_statement"], *recorded["required_complements"]}
            allowed |= required
            if (review["source"] != "independent-canonical"
                    or review["notes"] != recorded["analysis"]
                    or review["inherited_hypotheses"] != recorded["context_hypotheses"]
                    or not required <= selected):
                raise ValueError(f"A reviewed canonical clause or inherited premise was dropped: {label}")
        elif label in dense:
            recorded = dense[label]
            required = {r["declaration"] for r in recorded["recommended_terminal_bundle"]}
            allowed |= required
            expected_notes = {k: recorded[k] for k in ["objects", "hypotheses", "quantifier_order",
                               "semantic_comparison", "proof_closure", "scope_notes"]}
            if (review["source"] != "independent-dense" or review["notes"] != expected_notes
                    or review["inherited_hypotheses"] != recorded["hypotheses"]
                    or not required <= selected):
                raise ValueError(f"A reviewed dense-result clause or inherited premise was dropped: {label}")
        elif (review["source"] != "parent-source-type-definition-comparison"
              or review["notes"] != parent.get(row["number"])):
            raise ValueError(f"Parent source/type review changed: {label}")
        if not selected <= allowed:
            raise ValueError(f"Proof entry has no recorded association with this result: {label}")
        if row["printed_conditional_clause"] != (row["number"] in {"3.1", "15.13"}):
            raise ValueError(f"A printed conditional premise was relabelled: {label}")
        for entry in entries:
            name = entry["name"]
            info = compiled.get(name, {})
            if (name not in audit or info.get("kind") != "theorem"
                    or info.get("is_proposition") is not True):
                raise ValueError(f"Entry is not a source-audited compiled theorem: {name}")
            if entry["compiled_type_sha256"] != hashlib.sha256(info["type"].encode()).hexdigest():
                raise ValueError(f"Compiled theorem type changed: {name}")
            if any(entry[k] != locations.get(name, {}).get(k)
                   for k in ["source", "line", "source_sha256"]):
                raise ValueError(f"Theorem source hash or locator changed: {name}")
            if not entry["role"]:
                raise ValueError(f"Missing proof-entry role: {name}")
            distinct.add(name)
    objects = index["objects_not_proof_evidence"]
    if set(objects) & distinct:
        raise ValueError("A mathematical object was counted as proof evidence")
    if any(compiled.get(n, {}).get("kind") != "definition"
           or compiled.get(n, {}).get("is_proposition") is not False for n in objects):
        raise ValueError("The separate mathematical object inventory changed kind")
    if (len(objects) != 3 or set(objects) != {n for n, r in compiled.items()
                                             if r["kind"] == "definition"}
            or validation["compiled_types"] != len(compiled)
            or validation["propositions_audited"] != len(distinct)):
        raise ValueError("The compiled proof/object counts differ from the inventory")
    if distinct != {n for n, r in compiled.items() if r["kind"] == "theorem"}:
        raise ValueError("The compiled theorem inventory differs from the indexed entry points")
    return {"results": len(rows), "main": 73, "companion": 94,
            "distinct_proof_interfaces": len(distinct), "objects_not_proof_evidence": len(objects)}


def main():
    subprocess.run([sys.executable, str(ROOT / "scripts/check_revised_sources_v18.py"),
                    "--require-proved"], check=True)
    result = verify(json.loads(INDEX.read_text()))
    print(f"Verified all {result['results']} source-bound proof-entry bundles: "
          f"{result['main']} article and {result['companion']} companion results.")
    print(f"Actual compiled interfaces: {result['distinct_proof_interfaces']} theorems; "
          f"{result['objects_not_proof_evidence']} separate mathematical definitions.")
    print("Scope: source/type identity and recorded AI-assisted clause review; "
          "not a machine proof of TeX-to-Lean translation, human review or Palomar registration.")


if __name__ == "__main__":
    main()
