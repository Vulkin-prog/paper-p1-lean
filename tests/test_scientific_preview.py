"""Evidence controls for the strengthened manuscript; all mutations are in memory."""

from copy import deepcopy
from pathlib import Path
import json
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import check_scientific_preview as guard


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


class ScientificPreviewControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.files = guard.prior.Files()
        cls.final = cls.files.json(guard.PROPOSAL + "/final-validation.json")
        cls.review = cls.files.json(guard.PROPOSAL + "/independent-patch-review.json")

    def reject(self, path, value, reason):
        with self.assertRaisesRegex(ValueError, reason):
            guard.verify(guard.prior.Files(overrides={path: value}))

    def scope_control(self, edit_types=None, edit_log=None, exit_bytes=None, omit_read=False):
        record = deepcopy(self.final["bridge_compiled_scope"])
        review = deepcopy(self.review)
        types = self.files.json(record["path"])
        validation = self.files.json(record["validation_path"])
        folder = str(Path(record["path"]).parent)
        log_path = folder + "/compiled-types.log"
        log = self.files.text(log_path)
        if edit_types:
            edit_types(types)
        if edit_log:
            log = edit_log(log)
        types_bytes = encoded(types)
        validation["compiled_types_sha256"] = guard.prior.digest(types_bytes)
        validation["log_sha256"] = guard.prior.digest(log.encode())
        validation_bytes = encoded(validation)
        record["sha256"] = guard.prior.digest(types_bytes)
        record["validation_sha256"] = guard.prior.digest(validation_bytes)
        review["bridge_compiled_scope"]["sha256"] = record["sha256"]
        for row in review["bridge_inputs"]:
            if Path(row["path"]).name == "compiled-types.json":
                row["sha256"] = record["sha256"]
            if Path(row["path"]).name == "compiled-types-validation.json":
                row["sha256"] = record["validation_sha256"]
        if omit_read:
            review["bridge_compiled_entries_read"].pop()
        overrides = {record["path"]: types_bytes, record["validation_path"]: validation_bytes,
                     log_path: log.encode()}
        if exit_bytes is not None:
            overrides[folder + "/compiled-types.exit"] = exit_bytes
        return guard.reviewed_scope(guard.prior.Files(overrides=overrides), record, review, bridge=True)

    def test_current_review_and_all_prior_capsules_pass(self):
        result = guard.verify()
        self.assertEqual(result["current_targeted_propositions"], 15)
        self.assertEqual(result["pages"], 165)
        self.assertFalse(result["new_full_replay_claimed"])

    def test_unmodified_bridge_with_rebound_digests_passes(self):
        self.assertEqual(self.scope_control(), 3)

    def test_regular_domain_cannot_be_silently_dropped(self):
        path = guard.PACKAGE + "/sources/companion_sections/third_cumulant.tex"
        text = self.files.text(path)
        self.assertEqual(text.count(r"$T\subset G_N$"), 1)
        self.reject(path, text.replace(r"$T\subset G_N$", "$T$", 1).encode(), "Delivered strong manuscript")

    def test_separation_cannot_be_replaced_by_affine_compatibility(self):
        path = guard.PACKAGE + "/sources/companion_sections/third_cumulant.tex"
        text = self.files.text(path)
        self.assertEqual(text.count("the imposed\nseparation"), 1)
        self.reject(path, text.replace("the imposed\nseparation", "affine compatibility", 1).encode(), "Delivered strong manuscript")

    def test_weak_alias_alone_does_not_cover_the_sharp_one_target_clause(self):
        path = guard.PROPOSAL + "/preview-result-map.json"
        data = self.files.json(path)
        row = next(r for r in data["results"] if r["label"] == "p1:fixed:compressed")
        row["strengthened_or_additional_entry_points"] = ["PaperP1.FixedCompressedPrimitiveTheorem.companion_T4_4"]
        self.reject(path, encoded(data), "lacks its actual strong theorem")

    def test_wrong_logarithmic_note_source_is_rejected(self):
        path = guard.PROPOSAL + "/preview-result-map.json"
        data = self.files.json(path)
        row = next(r for r in data["results"] if r["label"] == "p13:rig:bcn")
        row["source"]["line"] += 1
        self.reject(path, encoded(data), "result locator differs")

    def test_rebound_changed_type_requires_the_independent_type_read(self):
        def change(types):
            types[0]["type"] = "True"
        with self.assertRaisesRegex(ValueError, "Reviewed compiled type"):
            self.scope_control(edit_types=change)

    def test_rebound_definition_cannot_count_as_a_theorem(self):
        def change(types):
            types[0]["kind"] = "definition"
        with self.assertRaisesRegex(ValueError, "mathematical role differs"):
            self.scope_control(edit_types=change)

    def test_rebound_axiom_log_cannot_hide_sorryAx(self):
        def change(log):
            self.assertIn("depends on axioms: [", log)
            return log.replace("depends on axioms: [", "depends on axioms: [sorryAx, ", 1)
        with self.assertRaisesRegex(ValueError, "incomplete or nonstandard"):
            self.scope_control(edit_log=change)

    def test_independent_bridge_read_cannot_omit_a_proposition(self):
        with self.assertRaisesRegex(ValueError, "Independent strengthened scope differs"):
            self.scope_control(omit_read=True)

    def test_nonzero_actual_extraction_exit_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "snapshot exit differs"):
            self.scope_control(exit_bytes=b"1\n")

    def test_frozen_receipt_cannot_inflate_proof_count(self):
        path = guard.PROPOSAL + "/final-validation.json"
        data = self.files.json(path)
        data["new_lean_theorems"] = 15
        self.reject(path, encoded(data), "Published scientific receipt changed")


if __name__ == "__main__":
    unittest.main()
