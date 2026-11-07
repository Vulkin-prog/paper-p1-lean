"""Reject stale or incomplete sharp-Palm proof correspondence without disk writes."""

from copy import deepcopy
from pathlib import Path
import json
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_manuscript_endpoints as guard


class SharpPalmControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.review = json.loads((ROOT / "docs/reviews/2026-11-07/sharp-good-edge-palm.json").read_text())
        cls.types = {r["name"]: r for r in json.loads((ROOT / "docs/validation/checkpoint-1005/scope/compiled-types.json").read_text())}
        cls.locations = guard.source_locations()
        cls.audit = set(json.loads((ROOT / "docs/axiom-audit-declarations.json").read_text()))

    def verify(self, review=None, types=None, locations=None, audit=None):
        return guard.sharp_palm_rows(self.review if review is None else review,
            self.types if types is None else types, self.locations if locations is None else locations,
            self.audit if audit is None else audit)

    def test_actual_four_interfaces_pass(self):
        self.verify()

    def test_finite_support_bridge_cannot_be_omitted(self):
        review = deepcopy(self.review)
        review["results"] = [r for r in review["results"] if not r["declaration"].endswith(".finite_mass")]
        with self.assertRaisesRegex(ValueError, "four interfaces"):
            self.verify(review=review)

    def test_changed_quantifier_type_requires_a_new_read(self):
        types = deepcopy(self.types)
        key = "PaperP1.SharpGoodEdgePositivePalm.uniform_normalized"
        types[key]["type"] = "True"
        with self.assertRaisesRegex(ValueError, "type/source/role"):
            self.verify(types=types)

    def test_definition_cannot_be_counted_as_a_proof(self):
        types = deepcopy(self.types)
        types[next(iter(types))]["kind"] = "definition"
        with self.assertRaisesRegex(ValueError, "type/source/role"):
            self.verify(types=types)

    def test_proposition_role_cannot_be_inferred_from_a_name(self):
        types = deepcopy(self.types)
        types[next(iter(types))]["is_proposition"] = False
        with self.assertRaisesRegex(ValueError, "type/source/role"):
            self.verify(types=types)

    def test_changed_body_is_not_covered_by_the_old_read(self):
        locations = deepcopy(self.locations)
        locations[next(iter(self.types))]["source_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "type/source/role"):
            self.verify(locations=locations)

    def test_unaudited_corollary_cannot_be_reported_complete(self):
        audit = self.audit - {"PaperP1.SharpGoodEdgePositivePalm.companion_T3_1_sharp"}
        with self.assertRaisesRegex(ValueError, "type/source/role"):
            self.verify(audit=audit)

    def test_an_unresolved_correction_prevents_acceptance(self):
        review = deepcopy(self.review)
        review["results"][0]["necessary_corrections"] = ["scope still unresolved"]
        with self.assertRaisesRegex(ValueError, "type/source/role"):
            self.verify(review=review)


if __name__ == "__main__":
    unittest.main()
