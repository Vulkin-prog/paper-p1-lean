#!/usr/bin/env python3
"""Verify the exact source/review chain of the three preserved editorial previews.

This read-only check reconstructs the reviewed patches and binds delivered
sources, PDF/build/visual records, compiled snapshots and the 167-result map.
It checks the evidence's integrity; semantic judgments remain in the frozen
AI-assisted reviews. It does not run Lean, LaTeX or a Palomar workflow.
"""

from collections import Counter
from pathlib import Path, PurePosixPath
import argparse
import gzip
import hashlib
import json
import re
import sys

sys.dont_write_bytecode = True
from check_revised_sources import PATTERN

ROOT = Path(__file__).resolve().parents[1]
PROPOSALS = "docs/editorial-proposals/2026-11-07"
BASE = "manuscripts/paper-p1/v1.8/sources"
STAGES = (
    ("simplification", "Condensed", "concise-proofs.patch", (65, 103), 120, 552, 12, 44, 0),
    ("structural-simplification", "Structural", "structural-simplifications.patch", (64, 102), 25, 552, 11, 44, 5),
    ("proof-simplification", "Simplified", "last-proof-cuts.patch", (64, 101), 132, 548, 11, 26, 30),
)
# Published final receipts are immutable capsules, not mutable progress flags.
# A further revision gets a new capsule rather than rewriting these records.
FROZEN_RECEIPTS = {
    "simplification": "32839c4a2f951d98169b661a69077de451f8436bf09f461b2b81d0df9464169c",
    "structural-simplification": "051d53700d6f9655a7b657cde271fe50bdeafa80e08ff808fdbbbb563644b783",
    "proof-simplification": "dd4b8ae602a0b67b2aa70c6cfade2f4dfaf73a9417c4f769a30d6c87b109c038",
}
REMOVED = {"p1:fixed:group-tail", "p1:fixed:component-kernel",
           "p1:fixed:high-hosts", "p1:fixed:very-high-hosts"}
PRECISIONS = {"p1:core:moderate", "p1:arith:alignedrank"}
ROOT_FILES = {"main.tex", "companion.tex", "preamble.tex"}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


class Files:
    """Read a repository snapshot; optional in-memory overlays support controls."""

    def __init__(self, root=ROOT, overrides=None):
        self.root = Path(root).resolve()
        self.overrides = overrides or {}
        self.cache = {}

    def local(self, name):
        require(isinstance(name, str) and name and "\\" not in name, "Invalid local path")
        p = PurePosixPath(name)
        require(not p.is_absolute() and ".." not in p.parts, f"Nonlocal evidence path: {name}")
        result = self.root / p
        require(result.resolve().is_relative_to(self.root), f"Evidence path escapes repository: {name}")
        return result

    def read(self, name):
        self.local(name)
        if name not in self.cache:
            data = self.overrides.get(name, ...)
            if data is ...:
                data = self.local(name).read_bytes()
            require(isinstance(data, bytes), f"Missing evidence file: {name}")
            self.cache[name] = data
        return self.cache[name]

    def text(self, name):
        return self.read(name).decode("utf-8")

    def json(self, name):
        return json.loads(self.text(name))

    def sha(self, name):
        return digest(self.read(name))

    def tex(self, directory):
        names = {str(p.relative_to(self.root)) for p in self.local(directory).rglob("*.tex")
                 if "build" not in p.relative_to(self.local(directory)).parts}
        for name, value in self.overrides.items():
            if name.startswith(directory + "/") and name.endswith(".tex"):
                if value is None:
                    names.discard(name)
                else:
                    names.add(name)
        return {name[len(directory) + 1:]: self.text(name) for name in sorted(names)}

    def binding(self, row, hash_key="sha256"):
        require(self.sha(row["path"]) == row[hash_key], f"Evidence digest changed: {row['path']}")
        return row["path"]


def apply_patch(sources, patch):
    """Apply exact unified hunks in memory, with no fuzzy matching or writes."""
    result = dict(sources)
    lines = patch.splitlines(keepends=True)
    cursor = 0
    changed = set()
    while cursor < len(lines):
        require(lines[cursor].startswith("--- a/"), "Expected a reviewed patch file header")
        name = lines[cursor][6:].rstrip("\n")
        require(name in sources and name not in changed, f"Unknown/duplicate patch source: {name}")
        require(cursor + 1 < len(lines) and lines[cursor + 1] == "+++ b/" + name + "\n",
                "Patch destination must equal its source")
        changed.add(name)
        cursor += 2
        original = sources[name].splitlines(keepends=True)
        output, position, hunks = [], 0, 0
        while cursor < len(lines) and lines[cursor].startswith("@@"):
            header = re.fullmatch(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@[^\n]*\n", lines[cursor])
            require(header is not None, "Malformed reviewed hunk")
            old_start, old_count, new_start, new_count = (int(v) if v is not None else 1 for v in header.groups())
            start = old_start - 1 if old_count else old_start
            require(position <= start <= len(original), "Overlapping/out-of-range patch hunk")
            output.extend(original[position:start])
            position = start
            require(len(output) == (new_start - 1 if new_count else new_start), "Incorrect new hunk position")
            cursor += 1
            old_seen = new_seen = 0
            while cursor < len(lines) and not lines[cursor].startswith(("@@", "--- a/")):
                line = lines[cursor]
                require(line[:1] in {" ", "+", "-"}, "Unsupported reviewed patch syntax")
                if line[0] in " -":
                    require(position < len(original) and original[position] == line[1:],
                            f"Reviewed patch context differs: {name}:{position + 1}")
                    position += 1
                    old_seen += 1
                if line[0] in " +":
                    output.append(line[1:])
                    new_seen += 1
                cursor += 1
            require((old_seen, new_seen) == (old_count, new_count), "Patch hunk count differs")
            hunks += 1
        require(hunks > 0, "A reviewed patch file has no hunk")
        output.extend(original[position:])
        result[name] = "".join(output)
    require(changed, "An editorial patch must contain a change")
    return result


def replace_once(text, before, after):
    require(text.count(before) == 1, "Presentation replacement does not have exactly one source")
    return text.replace(before, after, 1)


def pdf_name(style, document):
    return f"P1_{style}_Editorial_Preview_{'Main' if document == 'main' else 'Companion'}_2026-11-07_EN.pdf"


def presentation_copy(sources, style, previous):
    """Only the actual date, footer, metadata and cross-PDF substitutions."""
    result = dict(sources)
    for document in ["main", "companion"]:
        name = document + ".tex"
        text = result[name]
        old = f"{previous} editorial preview of working draft 1.8" if previous else "Working draft 1.8"
        text = replace_once(text, old, f"{style} editorial preview of working draft 1.8")
        other = "companion" if document == "main" else "main"
        old_pdf = pdf_name(previous, other) if previous else (
            "P1_V1_8_Technical_Companion_2026-11-07_EN.pdf" if other == "companion" else
            "P1_V1_8_Main_Article_2026-11-07_EN.pdf")
        text = replace_once(text, old_pdf, pdf_name(style, other))
        if document == "companion":
            old_title = f"Technical companion ({previous.lower()} editorial preview)" if previous else "Technical companion},pdfsubject"
            new_title = f"Technical companion ({style.lower()} editorial preview)" + ("" if previous else "},pdfsubject")
            text = replace_once(text, old_title, new_title)
        result[name] = text
    if previous:
        result["preamble.tex"] = sources["preamble.tex"].replace(
            f"{previous} editorial preview", f"{style} editorial preview").replace(
            f"{previous.lower()} editorial preview", f"{style.lower()} editorial preview")
    else:
        result["preamble.tex"] += (
            "\n% Presentation-only identifiers for the separate condensed preview.\n"
            "\\fancyfoot[L]{\\scriptsize\\color{black!60}Condensed editorial preview}\n"
            "\\hypersetup{pdftitle={Long multiplicative runs: condensed editorial preview},pdfkeywords={Condensed editorial preview; not an adopted manuscript revision}}\n")
    require({p for p in sources if sources[p] != result[p]} == ROOT_FILES, "Unexpected presentation root changes")
    return result


def source_hashes(sources):
    return {p: digest(t.encode()) for p, t in sources.items()}


def statements(sources):
    rows = {}
    for name, text in sources.items():
        for match in PATTERN.finditer(text):
            label = re.search(r"\\label\{([^}]+)\}", match.group())
            require(label is not None and label[1] not in rows, "Unlabelled/duplicate editorial result")
            rows[label[1]] = {"text": match.group(), "path": name,
                              "line": text[:match.start()].count("\n") + 1}
    require(len(rows) == 167, "An editorial preview must retain 167 numbered results")
    return rows


def labels(sources):
    return Counter(label for text in sources.values() for label in re.findall(r"\\label\{([^}]+)\}", text))


def review_pairs(review, before, after, stage):
    if stage == "proof-simplification":
        rows = review["mechanical_checks"]["changed_files"]
    else:
        rows = review["file_checks"]
    changed = {p for p in before if before[p] != after[p]}
    require(len(rows) == len(changed), "Review does not bind every changed scientific file")
    seen = set()
    for row in rows:
        name = row.get("file", row.get("path"))
        require(name in changed and name not in seen, "Duplicate/unreviewed scientific file")
        seen.add(name)
        old = row.get("before_sha256", row.get("clarified_sha256_reconstructed"))
        new = row.get("after_sha256", row.get("proposed_sha256_read"))
        require((old, new) == (digest(before[name].encode()), digest(after[name].encode())),
                f"Independent review preimage/image differs: {name}")


def scope_snapshot(files, record, review, count):
    path = files.binding(record)
    validation_path = record["validation_path"]
    require(files.sha(validation_path) == record["validation_sha256"], "Compiled validation digest differs")
    validation = files.json(validation_path)
    inventory = files.json(record["inventory_path"])
    compiled = files.json(path)
    require(len(inventory) == len(set(inventory)) == len(compiled) == count, "Compiled inventory count differs")
    require([r["name"] for r in compiled] == inventory, "Compiled snapshot inventory/order differs")
    require(validation["actual_exit_code"] == 0 and validation["all_propositions_standard_axioms_only"] is True,
            "Compiled snapshot lacks a successful standard-axiom extraction")
    folder = str(PurePosixPath(path).parent)
    log = files.text(folder + "/compiled-types.log")
    require(files.text(folder + "/compiled-types.exit").strip() == "0", "Compiled snapshot exit differs")
    require(validation["compiled_types_sha256"] == files.sha(path)
            and validation["inventory_sha256"] == files.sha(record["inventory_path"])
            and validation["log_sha256"] == files.sha(folder + "/compiled-types.log")
            and set(validation["permitted_axioms"]) == AXIOMS, "Compiled extraction inputs/log differ")
    propositions = {r["name"] for r in compiled if r["is_proposition"]}
    require(validation["compiled_types"] == count and validation["propositions_audited"] == len(propositions),
            "Compiled proposition count differs")
    require(record.get("types", record.get("existing_declarations")) == count
            and record["propositions_audited"] == len(propositions)
            and record["actual_exit_code"] == 0 and record["standard_axioms_only"] is True,
            "The receipt contradicts its actual compiled extraction")
    if "compiled_scope" in review:
        bound = review["compiled_scope"]
        require(bound["sha256"] == files.sha(path) and bound["validation_sha256"] == files.sha(validation_path)
                and bound["log_sha256"] == files.sha(folder + "/compiled-types.log"),
                "The independent scope read belongs to another extraction")
    else:
        bound = {PurePosixPath(r["path"]).name: r["sha256"] for r in review["inputs"]}
        require(bound["compiled-types.json"] == files.sha(path)
                and bound["compiled-types-validation.json"] == files.sha(validation_path),
                "The independent scope read belongs to another extraction")
    matches = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    axioms = {name: {a.strip() for a in raw.split(",") if a.strip()} for name, raw in matches}
    require(len(matches) == len(axioms) and set(axioms) == propositions
            and all(values <= AXIOMS for values in axioms.values()), "Actual axiom log is incomplete or nonstandard")
    reviewed = review.get("compiled_results", review.get("compiled_entries_read"))
    require(reviewed is not None and len(reviewed) == count, "Independent compiled scope read is incomplete")
    by_name = {r["name"]: r for r in compiled}
    require({r["declaration"] for r in reviewed} == set(by_name), "Reviewed compiled declarations differ")
    for row in reviewed:
        actual = by_name[row["declaration"]]
        require(row["compiled_type"] == actual["type"] and row["is_proposition"] == actual["is_proposition"]
                and not row["necessary_corrections"], "Reviewed compiled type or proposition role differs")
        require(actual["kind"] == ("theorem" if actual["is_proposition"] else "definition"),
                "A declaration's mathematical role differs")
        require(files.sha(row["file"]) == row["source_sha256"], "Reviewed Lean source changed")
        require(re.search(r"\b(?:theorem|lemma|def)\s+" + re.escape(row["declaration"].rsplit(".", 1)[1]) + r"\b",
                          files.text(row["file"]).splitlines()[row["line"] - 1]) is not None,
                "Reviewed Lean declaration location changed")
    return len(propositions)


def build_evidence(files, receipt, package, pages, contacts, details):
    require(files.read(package + "/PROVENANCE.json") == files.read(receipt), "Package provenance differs")
    final = files.json(receipt)
    build = files.json(package + "/validation/build-validation.json")
    render = files.json(package + "/validation/render-validation.json")
    visual = files.json(package + "/validation/visual-review.json")
    require(build["source_sha256"] == final["delivered_source_sha256"]
            and build["scientific_source_sha256"] == final["scientific_source_sha256"]
            and build["proof_source_commit"] == final["proof_source_commit"], "Build/source bindings differ")
    require(build["proposal_validation_sha256"] == final["frozen_initial_patch_validation"]["sha256"],
            "The PDF build belongs to a different proposed patch")
    require(build["numbered_labels_and_typeset_numbers_preserved"] == 167, "Typeset result-number check differs")
    rounds = build["actual_build_rounds"]
    require([(r["round"], r["document"]) for r in rounds] == [(i, d) for i in range(1, 4) for d in ["main", "companion"]]
            and all(r["actual_exit_code"] == 0 for r in rounds), "The six actual LaTeX executions did not pass")
    for key in ["overfull_boxes", "unresolved_references", "missing_glyphs"]:
        require(build[key] == final["compilation"][key] == 0, "The final PDF has unresolved build defects")
    require(final["pdfs"] == build["pdfs"], "Delivered and compiled PDF records differ")
    for document, page_count in zip(["main", "companion"], pages, strict=True):
        row = final["pdfs"][document]
        require(row["pages"] == page_count and files.sha(package + "/pdf/" + row["filename"]) == row["sha256"],
                "A delivered PDF differs from the checked artifact")
    require(visual == final["visual_review"] and visual["status"] == "passed"
            and visual["pages_rendered_and_contact_sheet_reviewed"] == sum(pages)
            and visual["contact_sheets_actually_inspected"] == contacts
            and visual["full_detail_pages_actually_inspected"] == details
            and visual["observed_clipping_overlap_or_missing_glyph_defects"] == 0,
            "The completed visual review is missing or belongs to another preview")
    if "pdf_sha256" in visual:
        require(visual["pdf_sha256"] == {key: row["sha256"] for key, row in final["pdfs"].items()},
                "Visual inspection belongs to different PDF bytes")
    require(render["pages_rendered"] == sum(pages) and render["detail_pages_rendered"] == details,
            "All-page rendering/detail counts differ")
    names = {r["filename"] for r in final["pdfs"].values()}
    for row in render["documents"]:
        require(not row["out_of_page_characters"] and not row["preview_marker_missing_pages"]
                and set(row["cross_pdf_file_targets"]) <= names, "Rendered page bounds/markers/links differ")
    logs = final["compilation"].get("logs")
    if logs:
        for row in logs.values():
            require(files.sha(row["path"]) == row["gzip_sha256"]
                    and digest(gzip.decompress(files.read(row["path"]))) == row["uncompressed_sha256"],
                    "A compressed raw LaTeX log changed")
    else:
        for row in final["compilation"]["final_logs"]:
            files.binding(row, "sha256_gzip")
            gzip.decompress(files.read(row["path"]))
    if "metadata_only_followup" in build:
        extra = build["metadata_only_followup"]
        require(extra == final["compilation"]["additional_metadata_only_compilation"]
                and extra["actual_exit_code"] == 0 and extra["all_auxiliary_bytes_unchanged"] is True
                and extra["page_count_unchanged"] is True, "The metadata-only PDF follow-up did not pass")


def verify(files=None):
    files = files or Files()
    endpoint = files.json("docs/manuscript-endpoints-v1.8.json")
    frozen = files.tex(BASE)
    require(len(frozen) == 48, "Frozen v1.8 must have 48 scientific sources")
    sources = dict(frozen)
    proposal = PROPOSALS + "/clarifications-and-finite-examples.patch"
    sources = apply_patch(sources, files.text(proposal))
    first = files.json(PROPOSALS + "/simplification/final-validation.json")
    proof_source = first["proof_source_commit"]
    require(re.fullmatch(r"[0-9a-f]{40}", proof_source) is not None, "Invalid historical proof source")
    require(first["prior_clarification_patch"]["path"] == proposal
            and first["prior_clarification_patch"]["sha256"] == files.sha(proposal), "Prior clarification patch changed")
    prior_statements = statements(sources)
    original_statements = statements(frozen)
    require(set(prior_statements) == set(original_statements)
            and {k for k in prior_statements if prior_statements[k]["text"] != original_statements[k]["text"]}
            == {"p13:transfer:small-kernels"}, "Initial clarification changes unexpected result blocks")
    previous_style, reports, audited = None, [], 0
    for stage, style, patch_name, pages, gain, label_count, contacts, details, count in STAGES:
        directory = PROPOSALS + "/" + stage
        receipt_path = directory + "/final-validation.json"
        require(files.sha(receipt_path) == FROZEN_RECEIPTS[stage], "A published final editorial receipt changed")
        receipt = files.json(receipt_path)
        package = f"manuscripts/paper-p1/editorial-{style.lower()}-preview-2026-11-07"
        require(receipt["package"] == package and receipt["proof_source_commit"] == proof_source,
                "Editorial package/proof source binding differs")
        review_path = files.binding(receipt["independent_concrete_diff_review"])
        review = files.json(review_path)
        require(review["status"] == "complete_frozen" and review["summary"]["mathematical_gaps_confirmed"] == 0
                and not review["necessary_corrections"] and review["proof_source_commit"] == proof_source,
                "Independent mathematical review is incomplete or belongs to another proof snapshot")
        require(review["summary"].get("patch_acceptable_mathematically") is True
                or review["summary"].get("verdict") == "acceptable_sur_le_plan_mathematique_et_editorial_dans_le_perimetre_relu",
                "The exact patch is not accepted in its frozen review")
        patch_path = directory + "/" + patch_name
        patch_record = receipt.get("patch", receipt.get("simplification_patch"))
        require(patch_record["path"] == patch_path, "Wrong patch bound to a preview")
        files.binding(patch_record)
        files.binding(receipt["frozen_initial_patch_validation"])
        initial_sha = receipt["frozen_initial_patch_validation"]["sha256"]
        manifest_path = package + "/SCIENTIFIC_SOURCE_MANIFEST.json"
        if "inputs" in review:
            inputs = {PurePosixPath(r["path"]).name: r["sha256"] for r in review["inputs"]}
            require(inputs[patch_name] == files.sha(patch_path) and inputs["patch-validation.json"] == initial_sha
                    and inputs["scientific-sources-manifest.json"] == files.sha(manifest_path), "Frozen diff inputs differ")
        else:
            require(review["patch"]["sha256"] == files.sha(patch_path)
                    and review["patch_validation"]["sha256"] == initial_sha
                    and review["scientific_manifest"]["sha256"] == files.sha(manifest_path), "Frozen diff inputs differ")
        scientific = apply_patch(sources, files.text(patch_path))
        review_pairs(review, sources, scientific, stage)
        require(source_hashes(scientific) == receipt["scientific_source_sha256"] == files.json(manifest_path),
                "The delivered science differs from the exact reviewed patch chain")
        require(sum(len(sources[p].splitlines()) - len(scientific[p].splitlines()) for p in sources) == gain,
                "The physical source-line gain differs")
        current = statements(scientific)
        require(set(current) == set(prior_statements), "A numbered result identity was removed or added")
        changed = {k for k in current if current[k]["text"] != prior_statements[k]["text"]}
        require(changed == (PRECISIONS if stage == "proof-simplification" else set()),
                "A numbered result changed beyond the independently reviewed conventions")
        old_labels, new_labels = labels(sources), labels(scientific)
        require(sum(new_labels.values()) == label_count and not new_labels - old_labels,
                "Unexpected new/missing TeX labels")
        require(set(old_labels - new_labels) == (REMOVED if stage == "proof-simplification" else set()),
                "The removed label set differs from the reviewed internal equations")
        for label in old_labels - new_labels:
            require(not any(label in text for text in scientific.values()), "A removed equation still has a reference")
        for text in scientific.values():
            require(all(target in new_labels for target in re.findall(r"\\(?:eqref|ref|pageref)\{([^}]+)\}", text)),
                    "A retained TeX reference is unresolved")
        predicted = presentation_copy(scientific, style, previous_style)
        delivered = files.tex(package + "/sources")
        require(predicted == delivered and len(delivered) == receipt["source_files"] == 48,
                "Delivered root/content changes exceed the reviewed science and exact presentation edits")
        require(source_hashes(delivered) == receipt["delivered_source_sha256"], "Delivered source manifest differs")
        plain_manifest = "".join(h + "  " + p + "\n" for p, h in sorted(source_hashes(delivered).items()))
        require(files.text(package + "/sources/MANIFEST_SHA256.txt") == plain_manifest, "Plain TeX manifest differs")
        build_evidence(files, receipt_path, package, pages, contacts, details)
        if count:
            audited += scope_snapshot(files, receipt["compiled_scope"], review, count)
        reports.append({"stage": stage, "receipt": receipt_path, "sha256": files.sha(receipt_path),
                        "pages": sum(pages), "labels": label_count, "source_lines_saved": gain})
        sources, prior_statements, previous_style = delivered, current, style
    verify_result_map(files, sources, endpoint, reports, proof_source)
    return {"status": "passed", "previews": reports, "numbered_results_each": 167,
            "scientific_sources_each": 48, "targeted_compiled_snapshot_records": 35,
            "audited_proposition_records": audited, "separate_definition_records": 1,
            "historical_compiled_snapshot_proof_source": proof_source,
            "total_source_lines_saved_after_clarifications": sum(r["source_lines_saved"] for r in reports),
            "latest_total_pages": reports[-1]["pages"], "scope": "Exact source/review/evidence integrity; semantic assessment is recorded separately. No new build or registration."}


def verify_result_map(files, sources, endpoint, reports, proof_source):
    latest = PROPOSALS + "/proof-simplification/preview-result-map.json"
    mapping = files.json(latest)
    rows = mapping["results"]
    actual = statements(sources)
    original = {r["label"]: r for r in endpoint["results"]}
    require(len(rows) == len({r["label"] for r in rows}) == 167 and {r["label"] for r in rows} == set(actual),
            "The latest result map is incomplete")
    require(Counter(r["document"] for r in rows) == {"main": 73, "companion": 94}, "Result-map document partition differs")
    package = "manuscripts/paper-p1/editorial-simplified-preview-2026-11-07"
    for row in rows:
        label, source = row["label"], row["source"]
        require(row["number"] == original[label]["number"] and row["document"] == original[label]["document"],
                "A mapped result identity/number differs")
        require(row["proof_source_commit"] == proof_source, "Mapped historical proof snapshot differs")
        require(source["path"] == package + "/sources/" + actual[label]["path"]
                and source["line"] == actual[label]["line"] and source["file_sha256"] == files.sha(source["path"])
                and source["statement_sha256"] == digest(actual[label]["text"].encode()), "A mapped result source differs")
        require(row["existing_proof_bundle"]["entry_points"] == [r["name"] for r in original[label]["entry_points"]],
                "A mapped proof bundle differs")
        for entry in original[label]["entry_points"]:
            require(files.sha(entry["source"]) == entry["source_sha256"], "A mapped Lean proof source changed")
    integration = files.json(PROPOSALS + "/integration-status.json")
    proposals = integration["proposals"]
    require(integration["proposal_count"] == integration["applied_count"] == len(proposals) == 13
            and {r["id"] for r in proposals} == {f"SIM{i:02}" for i in range(1, 14)}, "Thirteen-proposal integration is incomplete")
    for row in proposals:
        number = int(row["id"][3:])
        stage = reports[0 if number <= 8 else 1 if number <= 11 else 2]
        require(row["stage"] == stage["stage"] and row["validation"] == {"path": stage["receipt"], "sha256": stage["sha256"]},
                "An applied proposal points to the wrong verified stage")
    require(integration["latest_package"] == package and integration["palomar_status"] == "on_hold_at_user_request",
            "The latest editorial integration state differs")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Print the read-only verification result as JSON")
    args = parser.parse_args()
    result = verify()
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        print("Verified all three editorial previews by exact in-memory patch reconstruction.")
        print("Each retains 167 result identities and 48 sources; latest preview: 165 pages and 548 labels.")
        print("Compiled scope records: 35, including 34 audited propositions and one separate definition.")
        print("Scope: source/review/evidence integrity; the semantic review remains distinct.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, UnicodeError, IndexError, TypeError) as error:
        raise SystemExit(f"Editorial preview integrity check failed: {error}") from error
