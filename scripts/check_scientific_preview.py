#!/usr/bin/env python3
"""Bind the strengthened manuscript to its frozen diff, review and Lean snapshots.

Read-only evidence integrity, not automatic semantic verification of TeX and
not a new Lean/LaTeX build or Palomar action. Prior capsules remain immutable.
"""

from collections import Counter
from copy import deepcopy
from pathlib import PurePosixPath
import argparse
import json
import re
import sys

sys.dont_write_bytecode = True
import check_editorial_previews as prior

PROPOSAL = prior.PROPOSALS + "/scientific-strengthening"
PACKAGE = "manuscripts/paper-p1/editorial-strengthened-preview-2026-11-07"
BASE_PACKAGE = "manuscripts/paper-p1/editorial-simplified-preview-2026-11-07"
RECEIPT_SHA256 = "cc304ed893330c93883b0d92b8f6b8a6dc0b8e1da1d64ec1d0556bd4a9f196c4"
CHANGED = {"p13:rig:local-square", "p1:arith:fixed-support", "p1:fixed:compressed"}
STRONG = {
    "p13:rig:local-square": {"PaperP1.LocalSquareThreshold.local_square_threshold_power_five"},
    "p1:arith:fixed-support": {"PaperP1.SeveralWindowProjectionCount.companion_T1_14",
        "PaperP1.BlockSupportCount.critical_interval_count", "PaperP1.BlockSupportParameters.critical_count"},
    "p1:fixed:compressed": {"PaperP1.EffectiveCompressedPrimitiveMass.uniform_mass",
        "PaperP1.FixedCompressedPrimitiveTheorem.companion_T4_4",
        "PaperP1.HomogeneousEffectiveGoodPairExtensions.uniform_mass",
        "PaperP1.HomogeneousEffectiveConnectedChannel.uniform_mass",
        "PaperP1.HomogeneousRunMass.actual_joint_le", "PaperP1.HomogeneousRunMass.probability_rank"},
    "p13:rig:bcn": {"PaperP1.IntegralAffineCurvePointCount.grid_bound",
        "PaperP1.IntegralAffineCurvePointCount.finite_population", "PaperP1.UniformIntegralCurveCount.realConstant_pos"},
}
require = prior.require


def reviewed_scope(files, record, review, *, bridge=False):
    """Adapt the new frozen review's explicit schema to the shared scope gate."""
    entries = review["bridge_compiled_entries_read" if bridge else "compiled_entries_read"]
    inputs = review["bridge_inputs" if bridge else "inputs"]
    bound = review["bridge_compiled_scope" if bridge else "compiled_scope"]
    count = 3 if bridge else 12
    require(len(entries) == count and bound["types"] == bound["propositions"] == count
            and bound["sha256"] == files.sha(record["path"]), "Independent strengthened scope differs")
    verdict = "conforme_au_raccord_positif_et_affine" if bridge else "conforme_au_role_propose"
    require(all(row["verdict"] == verdict and row["body_comparison"]
                and row["source_byte_identical_to_proof_commit"] is True for row in entries),
            "An independent body/role comparison is missing")
    normalized = {"inputs": inputs, "compiled_entries_read": deepcopy(entries)}
    for row in normalized["compiled_entries_read"]:
        row["necessary_corrections"] = []
    return prior.scope_snapshot(files, record, normalized, count)


def verify_result_map(files, sources, compiled):
    mapping = files.json(PROPOSAL + "/preview-result-map.json")
    actual = prior.statements(sources)
    base = prior.statements(files.tex(BASE_PACKAGE + "/sources"))
    frozen = prior.statements(files.tex(prior.BASE))
    changes = files.json(PROPOSAL + "/amendments.json")["amendments"]
    old = {r["label"]: r for r in files.json(prior.PROPOSALS + "/proof-simplification/preview-result-map.json")["results"]}
    rows = mapping["results"]
    require(mapping["package"] == PACKAGE and len(rows) == len({r["label"] for r in rows}) == 167
            and {r["label"] for r in rows} == set(actual), "Strengthened result map is incomplete")
    require(Counter(r["document"] for r in rows) == {"main": 73, "companion": 94}, "Result partition differs")
    for row in rows:
        label, source = row["label"], row["source"]
        require((row["number"], row["document"], row["proof_source_commit"]) ==
                (old[label]["number"], old[label]["document"], old[label]["proof_source_commit"]),
                "A strengthened result identity or proof snapshot differs")
        require(source == {"path": PACKAGE + "/sources/" + actual[label]["path"],
                "line": actual[label]["line"], "file_sha256": files.sha(PACKAGE + "/sources/" + actual[label]["path"]),
                "statement_sha256": prior.digest(actual[label]["text"].encode())}, "Strengthened result locator differs")
        require(row["existing_proof_bundle"]["entry_points"] == old[label]["existing_proof_bundle"]["entry_points"],
                "A preserved clause bundle was replaced")
        require(row["frozen_v18_statement_unchanged"] == (actual[label]["text"] == frozen[label]["text"])
                and row["simplified_stage_statement_unchanged"] == (actual[label]["text"] == base[label]["text"])
                and row["scientific_amendments"] == [r["id"] for r in changes if r["label"] == label],
                "A strengthened source/amendment disposition differs")
        stronger = row["strengthened_or_additional_entry_points"]
        require(len(stronger) == len(set(stronger)) and set(stronger) == STRONG.get(label, set())
                and set(stronger) <= compiled, "A strengthened clause lacks its actual strong theorem")


def verify(files=None):
    files = files or prior.Files()
    previous = prior.verify(files)
    receipt_path = PROPOSAL + "/final-validation.json"
    require(files.sha(receipt_path) == RECEIPT_SHA256, "Published scientific receipt changed")
    final = files.json(receipt_path)
    require(final["package"] == PACKAGE and final["base_package"] == BASE_PACKAGE
            and files.read(PACKAGE + "/PROVENANCE.json") == files.read(receipt_path), "Scientific package provenance differs")
    require(final["proof_source_commit"] == previous["historical_compiled_snapshot_proof_source"]
            and final["new_lean_theorems"] == final["new_ledger_entries"] == 0,
            "An editorial reuse was counted as a new proof replay")
    require(final["palomar_status"] == "on_hold_at_user_request" and final["registry_scopes_changed"] is False,
            "Registry hold/scope differs")
    review = files.json(files.binding(final["independent_concrete_diff_review"]))
    require(review["status"] == "complete_frozen" and review["summary"]["mathematical_gaps_confirmed"] == 0
            and review["summary"]["necessary_corrections"] == 0 and not review["necessary_corrections"]
            and review["summary"]["verdict"] == "accepte_sur_le_plan_mathematique_et_editorial_dans_le_perimetre_relu"
            and review["proof_source_commit"] == final["proof_source_commit"], "Scientific diff review is not accepted")
    preliminary = files.json(files.binding(final["preliminary_review"]))
    patch_path = files.binding(final["patch"])
    initial_path = files.binding(final["frozen_initial_patch_validation"])
    require(review["patch_sha256"] == files.sha(patch_path), "Independent diff digest differs")
    inputs = {PurePosixPath(r["path"]).name: r["sha256"] for r in review["inputs"]}
    manifest = PACKAGE + "/SCIENTIFIC_SOURCE_MANIFEST.json"
    require(inputs["scientific-strengthenings.patch"] == files.sha(patch_path)
            and inputs["patch-validation.json"] == files.sha(initial_path)
            and inputs["scientific-sources-manifest.json"] == files.sha(manifest), "Reviewed scientific inputs differ")
    before = files.tex(BASE_PACKAGE + "/sources")
    science = prior.apply_patch(before, files.text(patch_path))
    prior.review_pairs(review, before, science, "proof-simplification")
    require(prior.source_hashes(science) == final["scientific_source_sha256"] == files.json(manifest),
            "Strong manuscript differs from the reviewed scientific patch")
    actual = files.tex(PACKAGE + "/sources")
    require(len(actual) == 48 and actual == prior.presentation_copy(science, "Strengthened", "Simplified")
            and prior.source_hashes(actual) == final["delivered_source_sha256"],
            "Delivered strong manuscript differs from reviewed content/presentation")
    plain = "".join(h + "  " + p + "\n" for p, h in sorted(prior.source_hashes(actual).items()))
    require(files.text(PACKAGE + "/sources/MANIFEST_SHA256.txt") == plain, "Strong source manifest differs")
    old_statements, new_statements = prior.statements(before), prior.statements(actual)
    require(set(new_statements) == set(old_statements)
            and {k for k in new_statements if new_statements[k]["text"] != old_statements[k]["text"]} == CHANGED,
            "Unexpected strengthened numbered statements")
    require(prior.labels(before) == prior.labels(actual) and sum(prior.labels(actual).values()) == 548,
            "Strong manuscript labels differ")
    for text in actual.values():
        require(all(target in prior.labels(actual) for target in re.findall(r"\\(?:ref|eqref|pageref)\{([^}]+)\}", text)),
                "Strong manuscript has an unresolved reference")
    count = reviewed_scope(files, final["compiled_scope"], review)
    count += reviewed_scope(files, final["bridge_compiled_scope"], review, bridge=True)
    compiled = {r["name"] for field in ["compiled_scope", "bridge_compiled_scope"] for r in files.json(final[field]["path"])}
    verify_result_map(files, actual, compiled)
    amendments = files.json(PROPOSAL + "/amendments.json")
    require(len(amendments["amendments"]) == 5 and {r["id"] for r in amendments["amendments"]}
            == {f"SCI{i:02}" for i in range(1, 6)}, "Scientific amendment inventory differs")
    ledger = {r["id"] for r in files.json("docs/mathematical-changes.json")["findings"]}
    require(all(set(r["ledger_ids"]) <= ledger and set(r["declarations"]) <= compiled for r in amendments["amendments"]),
            "An amendment has no existing ledger/proof evidence")
    for label, names in STRONG.items():
        require({n for r in amendments["amendments"] if r["label"] == label for n in r["declarations"]} == names,
                "An amendment lost its strong declaration")

    build = files.json(PACKAGE + "/validation/build-validation.json")
    render = files.json(PACKAGE + "/validation/render-validation.json")
    visual = files.json(PACKAGE + "/validation/visual-review.json")
    require(build["source_sha256"] == final["delivered_source_sha256"]
            and build["scientific_source_sha256"] == final["scientific_source_sha256"]
            and build["proof_source_commit"] == final["proof_source_commit"]
            and build["proposal_validation_sha256"] == files.sha(initial_path), "Strong PDF build source differs")
    require(build["actual_build_rounds"] == [{"document": d, "round": i, "actual_exit_code": 0}
            for i in range(1, 4) for d in ["main", "companion"]]
            and build["numbered_labels_and_typeset_numbers_preserved"] == 167, "Strong PDF build did not pass")
    require(final["pdfs"] == build["pdfs"] and [build["pdfs"][d]["pages"] for d in ["main", "companion"]] == [64, 101],
            "Strong PDF page counts differ")
    for field in ["overfull_boxes", "unresolved_references", "missing_glyphs"]:
        require(build[field] == final["compilation"][field] == 0, "Strong PDF has unresolved build defects")
    for row in final["pdfs"].values():
        require(files.sha(PACKAGE + "/pdf/" + row["filename"]) == row["sha256"], "Strong PDF bytes differ")
    for row in final["compilation"]["logs"].values():
        require(files.sha(row["path"]) == row["gzip_sha256"]
                and prior.digest(prior.gzip.decompress(files.read(row["path"]))) == row["uncompressed_sha256"],
                "Strong raw build log differs")
    require(visual == final["visual_review"] and visual["status"] == "passed"
            and visual["pages_rendered_and_contact_sheet_reviewed"] == render["pages_rendered"] == 165
            and visual["contact_sheets_actually_inspected"] == 11
            and visual["full_detail_pages_actually_inspected"] == len(visual["detail_pages_actually_inspected"]) == 29
            and visual["detail_pages_rendered"] == render["detail_pages_rendered"] == 63
            and visual["observed_clipping_overlap_or_missing_glyph_defects"] == 0
            and visual["pdf_sha256"] == {k: r["sha256"] for k, r in final["pdfs"].items()},
            "Completed strong PDF visual review differs")
    names = {r["filename"] for r in final["pdfs"].values()}
    for row in render["documents"]:
        require(not row["out_of_page_characters"] and not row["preview_marker_missing_pages"]
                and set(row["cross_pdf_file_targets"]) <= names, "Strong PDF bounds/markers/links differ")
    imports = files.json(PROPOSAL + "/one-target-import-evidence.json")
    require(files.sha(PROPOSAL + "/one-target-import-evidence.json") == preliminary["import_evidence"]["sha256"]
            and imports["local_import_ancestors"] == 1486 and not imports["forbidden_or_potentially_circular_ancestors"]
            and len(imports["module_source_sha256"]) == 1487, "Positive one-target import evidence differs")
    for module, h in imports["module_source_sha256"].items():
        require(files.sha(module.replace(".", "/") + ".lean") == h, "Positive one-target proof dependency changed")
    return {"status": "passed", "prior_simplification_previews": 3, "strengthened_previews": 1,
            "numbered_results": 167, "changed_numbered_statements": sorted(CHANGED), "labels": 548,
            "current_targeted_types": count, "current_targeted_propositions": count, "pages": 165,
            "historical_full_proof_source": final["proof_source_commit"], "new_full_replay_claimed": False,
            "palomar_status": final["palomar_status"], "scope": "Exact reviewed source/type/evidence integrity; semantic review remains separate."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = verify()
    print(json.dumps(result, ensure_ascii=False, indent=2) if args.json else
          "Verified strengthened preview: 167 results, 548 labels, 15 existing audited propositions, 165 pages. Palomar on hold.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, UnicodeError, IndexError, TypeError) as error:
        raise SystemExit(f"Scientific preview integrity check failed: {error}") from error
