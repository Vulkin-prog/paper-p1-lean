"""Meaningful in-memory controls for reviewed manuscript/proof correspondence.

No manuscript, frozen report, compiled snapshot or PDF is modified on disk.
The scope controls deliberately rebind file digests before exercising the
semantic-role/axiom/type gates, so they do not merely test stale hashes.
"""

from copy import deepcopy
from pathlib import Path
import json
import re
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import check_editorial_previews as guard

PROPOSAL = guard.PROPOSALS + "/proof-simplification"
PACKAGE = "manuscripts/paper-p1/editorial-simplified-preview-2026-11-07"


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


class EditorialPreviewControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = guard.Files()
        cls.final = cls.original.json(PROPOSAL + "/final-validation.json")
        cls.review = cls.original.json(PROPOSAL + "/independent-patch-review.json")

    def reject_overlay(self, path, data, reason):
        with self.assertRaisesRegex(ValueError, reason):
            guard.verify(guard.Files(overrides={path: data}))

    def scope_control(self, *, edit_types=None, edit_log=None, edit_validation=None,
                      edit_record=None, exit_bytes=None):
        record = deepcopy(self.final["compiled_scope"])
        review = deepcopy(self.review)
        types = self.original.json(record["path"])
        validation = self.original.json(record["validation_path"])
        folder = str(Path(record["path"]).parent)
        log_path = folder + "/compiled-types.log"
        log = self.original.text(log_path)
        if edit_types:
            edit_types(types)
        if edit_log:
            log = edit_log(log)
        types_bytes, log_bytes = encoded(types), log.encode()
        validation["compiled_types_sha256"] = guard.digest(types_bytes)
        validation["log_sha256"] = guard.digest(log_bytes)
        if edit_validation:
            edit_validation(validation)
        validation_bytes = encoded(validation)
        record["sha256"] = guard.digest(types_bytes)
        record["validation_sha256"] = guard.digest(validation_bytes)
        if edit_record:
            edit_record(record)
        for row in review["inputs"]:
            if Path(row["path"]).name == "compiled-types.json":
                row["sha256"] = guard.digest(types_bytes)
            if Path(row["path"]).name == "compiled-types-validation.json":
                row["sha256"] = guard.digest(validation_bytes)
        overrides = {record["path"]: types_bytes, record["validation_path"]: validation_bytes,
                     log_path: log_bytes}
        if exit_bytes is not None:
            overrides[folder + "/compiled-types.exit"] = exit_bytes
        return guard.scope_snapshot(guard.Files(overrides=overrides), record, review, 30)

    def test_current_three_previews_pass(self):
        result = guard.verify()
        self.assertEqual([r["pages"] for r in result["previews"]], [168, 166, 165])
        self.assertEqual(result["audited_proposition_records"], 34)
        self.assertEqual(result["total_source_lines_saved_after_clarifications"], 277)

    def test_rebound_unmodified_scope_passes(self):
        self.assertEqual(self.scope_control(), 29)

    def test_historical_scopes_do_not_become_a_new_proof_replay(self):
        path = "docs/manuscript-endpoints-v1.8.json"
        changed = self.original.json(path)
        changed["proof_source_commit"] = "f" * 40
        # The old source/type map still has its own immutable proof snapshot.
        # The separate complete manuscript gate validates any new live header.
        result = guard.verify(guard.Files(overrides={path: encoded(changed)}))
        self.assertEqual(result["historical_compiled_snapshot_proof_source"], self.final["proof_source_commit"])

    def test_autonomous_compressed_proof_cannot_disappear_after_review(self):
        path = PACKAGE + "/sources/companion_sections/fixed_moments.tex"
        text = self.original.text(path)
        before = "Theorem~\\ref{p13:half:conditional}, with no old\nsources"
        self.assertEqual(text.count(before), 1)
        self.reject_overlay(path, text.replace(before, "The preceding proof", 1).encode(), "Delivered root/content")

    def test_distinct_window_convention_cannot_be_dropped(self):
        path = PACKAGE + "/sources/main_sections/cores.tex"
        text = self.original.text(path)
        self.assertEqual(text.count("$r$ distinct original windows"), 1)
        self.reject_overlay(path, text.replace("$r$ distinct original windows", "$r$ original windows").encode(),
                            "Delivered root/content")

    def test_enlarged_cutoff_cannot_be_silently_broadened(self):
        path = PACKAGE + "/sources/companion_sections/arithmetic_appendix.tex"
        text = self.original.text(path)
        self.assertEqual(text.count("$6bB\\le H\\le DB$"), 1)
        self.reject_overlay(path, text.replace("$6bB\\le H\\le DB$", "$B\\le H\\le DB$").encode(),
                            "Delivered root/content")

    def test_missing_source_is_rejected(self):
        self.reject_overlay(PACKAGE + "/sources/main_sections/cores.tex", None, "Delivered root/content")

    def test_missing_numbered_result_is_rejected(self):
        path = PACKAGE + "/sources/main_sections/cores.tex"
        text = self.original.text(path)
        match = next(m for m in guard.PATTERN.finditer(text) if "p1:core:moderate" in m.group())
        self.reject_overlay(path, (text[:match.start()] + text[match.end():]).encode(), "Delivered root/content")

    def test_preamble_changes_are_not_arbitrary_presentation_edits(self):
        path = PACKAGE + "/sources/preamble.tex"
        self.reject_overlay(path, self.original.read(path) + b"\\renewcommand{\\epsilon}{0}\n", "Delivered root/content")

    def test_pdf_bytes_remain_the_inspected_bytes(self):
        path = PACKAGE + "/pdf/" + self.final["pdfs"]["companion"]["filename"]
        self.reject_overlay(path, self.original.read(path) + b"changed", "delivered PDF differs")

    def test_published_receipts_are_immutable(self):
        path = PROPOSAL + "/final-validation.json"
        value = self.original.json(path)
        value["scope"] += " changed"
        self.reject_overlay(path, encoded(value), "published final editorial receipt changed")

    def test_replica_formula_cannot_replace_propagation_and_moments(self):
        path = PROPOSAL + "/preview-result-map.json"
        value = self.original.json(path)
        row = next(r for r in value["results"] if r["label"] == "p1:uniform:replicas")
        self.assertGreater(len(row["existing_proof_bundle"]["entry_points"]), 1)
        row["existing_proof_bundle"]["entry_points"] = row["existing_proof_bundle"]["entry_points"][:1]
        self.reject_overlay(path, encoded(value), "mapped proof bundle differs")

    def test_result_number_cannot_be_reassigned(self):
        path = PROPOSAL + "/preview-result-map.json"
        value = self.original.json(path)
        value["results"][0]["number"] = "changed"
        self.reject_overlay(path, encoded(value), "mapped result identity/number differs")

    def test_result_source_locator_cannot_drift(self):
        path = PROPOSAL + "/preview-result-map.json"
        value = self.original.json(path)
        value["results"][0]["source"]["line"] += 1
        self.reject_overlay(path, encoded(value), "mapped result source differs")

    def test_sim13_cannot_be_reported_as_an_earlier_uncoupled_cut(self):
        path = guard.PROPOSALS + "/integration-status.json"
        value = self.original.json(path)
        row = next(r for r in value["proposals"] if r["id"] == "SIM13")
        row["stage"] = "simplification"
        row["validation"] = deepcopy(value["proposals"][0]["validation"])
        self.reject_overlay(path, encoded(value), "wrong verified stage")

    def test_omitting_one_simplification_is_rejected(self):
        path = guard.PROPOSALS + "/integration-status.json"
        value = self.original.json(path)
        value["proposals"].pop()
        self.reject_overlay(path, encoded(value), "Thirteen-proposal integration is incomplete")

    def test_rebound_definition_cannot_be_called_a_theorem(self):
        def mutate(rows):
            row = next(r for r in rows if not r["is_proposition"])
            row["kind"] = "theorem"
        with self.assertRaisesRegex(ValueError, "mathematical role differs"):
            self.scope_control(edit_types=mutate)

    def test_rebound_type_requires_the_independent_type_read(self):
        with self.assertRaisesRegex(ValueError, "Reviewed compiled type"):
            self.scope_control(edit_types=lambda rows: rows[0].update(type="True"))

    def test_rebound_axiom_log_cannot_introduce_sorryAx(self):
        def mutate(log):
            changed, count = re.subn(r"depends on axioms: \[", "depends on axioms: [sorryAx, ", log, count=1)
            self.assertEqual(count, 1)
            return changed
        with self.assertRaisesRegex(ValueError, "Actual axiom log"):
            self.scope_control(edit_log=mutate)

    def test_rebound_axiom_log_must_cover_every_proposition(self):
        def mutate(log):
            pattern = r"^.*'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms).*\n"
            changed, count = re.subn(pattern, "", log, count=1, flags=re.M)
            self.assertEqual(count, 1)
            return changed
        with self.assertRaisesRegex(ValueError, "Actual axiom log"):
            self.scope_control(edit_log=mutate)

    def test_rebound_failed_extraction_cannot_be_counted_as_success(self):
        with self.assertRaisesRegex(ValueError, "successful standard-axiom extraction"):
            self.scope_control(edit_validation=lambda v: v.update(actual_exit_code=1))

    def test_actual_exit_file_must_also_report_success(self):
        with self.assertRaisesRegex(ValueError, "Compiled snapshot exit differs"):
            self.scope_control(exit_bytes=b"1\n")

    def test_receipt_cannot_inflate_the_compiled_count(self):
        with self.assertRaisesRegex(ValueError, "receipt contradicts its actual compiled extraction"):
            self.scope_control(edit_record=lambda r: r.update(existing_declarations=31))

    def test_missing_compiled_declaration_is_rejected_after_rebinding(self):
        with self.assertRaisesRegex(ValueError, "Compiled inventory count differs"):
            self.scope_control(edit_types=lambda rows: rows.pop())

    def test_reviewed_lean_body_cannot_change_behind_the_same_type(self):
        path = "PaperP1/Asymptotics/ModerateCertificateAsymptotic.lean"
        self.reject_overlay(path, self.original.read(path) + b"\n-- body changed after review\n", "Reviewed Lean source changed")

    def test_fuzzy_patch_context_is_not_accepted(self):
        patch = "--- a/a.tex\n+++ b/a.tex\n@@ -1 +1 @@\n-wrong\n+new\n"
        with self.assertRaisesRegex(ValueError, "patch context differs"):
            guard.apply_patch({"a.tex": "old\n"}, patch)

    def test_patch_cannot_target_a_file_outside_the_scientific_copy(self):
        patch = "--- a/../AGENTS.md\n+++ b/../AGENTS.md\n@@ -1 +1 @@\n-old\n+new\n"
        with self.assertRaisesRegex(ValueError, "Unknown/duplicate patch source"):
            guard.apply_patch({"a.tex": "old\n"}, patch)
        with self.assertRaisesRegex(ValueError, "Nonlocal evidence path"):
            guard.Files().read("../AGENTS.md")

    def test_hunk_counts_must_match_actual_content(self):
        patch = "--- a/a.tex\n+++ b/a.tex\n@@ -1,2 +1 @@\n-old\n+new\n"
        with self.assertRaisesRegex(ValueError, "hunk count differs"):
            guard.apply_patch({"a.tex": "old\n"}, patch)

    def test_hunks_cannot_skip_to_unrelated_text(self):
        patch = "--- a/a.tex\n+++ b/a.tex\n@@ -99 +1 @@\n-old\n+new\n"
        with self.assertRaisesRegex(ValueError, "out-of-range patch hunk"):
            guard.apply_patch({"a.tex": "old\n"}, patch)


if __name__ == "__main__":
    unittest.main()
