"""Counterfactual scope changes must fail without mutating repository files."""
import copy
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_manuscript_v20 import check_partition, check_semantics


class V2ScopeControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.index = json.loads((ROOT / 'docs/manuscript-results-v2.0.json').read_text())
        cls.old = {r['label']: r for r in json.loads((ROOT / 'docs/manuscript-endpoints-v1.8.json').read_text())['results']}
        cls.types = {r['name']: r for r in json.loads((ROOT / 'docs/validation/v2.0/v2-scope/compiled-types.json').read_text())}

    def type_change_fails(self, name, change):
        types = copy.deepcopy(self.types)
        change(types[name])
        with self.assertRaises(ValueError):
            check_semantics(types)

    def test_current_scope_passes(self):
        check_partition(self.index, self.old)
        check_semantics(self.types)

    def test_a_retired_result_is_not_false(self):
        data = copy.deepcopy(self.index)
        data['retired_historical_results'][0]['invalidated_by_v2'] = True
        with self.assertRaises(ValueError):
            check_partition(data, self.old)

    def test_historical_result_cannot_disappear(self):
        data = copy.deepcopy(self.index)
        data['retired_historical_results'].pop()
        with self.assertRaises(ValueError):
            check_partition(data, self.old)

    def test_strong_compressed_clause_cannot_be_dropped(self):
        data = copy.deepcopy(self.index)
        row = next(r for r in data['results'] if r['label'] == 'p1:fixed:compressed')
        row['entry_points'] = row['entry_points'][:1]
        with self.assertRaises(ValueError):
            check_partition(data, self.old)

    def test_local_power_five_cannot_use_only_weaker_alias(self):
        data = copy.deepcopy(self.index)
        row = next(r for r in data['results'] if r['label'] == 'p13:rig:local-square')
        row['entry_points'].pop()
        with self.assertRaises(ValueError):
            check_partition(data, self.old)

    def test_conditional_transfer_is_not_unconditional(self):
        data = copy.deepcopy(self.index)
        next(r for r in data['results'] if r['label'] == 'p13:transfer:finite')['printed_conditional_clause'] = False
        with self.assertRaises(ValueError):
            check_partition(data, self.old)

    def test_no_hidden_target_bound_as_a_premise(self):
        self.type_change_fails('PaperP1.AllTargetGoodEdgePalm.companion_T10_5',
                               lambda row: row['binders'].append({'name': 'assumed_target_estimate'}))

    def test_palm_target_regularity_is_a_scope_loss(self):
        self.type_change_fails('PaperP1.AllTargetGoodEdgePalm.companion_T10_5',
                               lambda row: row.update(type=row['type'].replace('PaperP1.Model.dyadicBlock N', 'PaperP1.RegularStarts.regularStarts N L')))

    def test_beta_positive_before_division_is_required(self):
        self.type_change_fails('PaperP1.AllTargetGoodEdgePalm.companion_T10_5',
                               lambda row: row.update(type=row['type'].replace('0 < PaperP1.GoodEdgePositivePalm.beta', '0 ≤ PaperP1.GoodEdgePositivePalm.beta')))

    def test_palm_must_bound_sum_of_both_centerings(self):
        self.type_change_fails('PaperP1.AllTargetGoodEdgePalm.companion_T10_5',
                               lambda row: row.update(type=row['type'].replace('AllTargetGoodEdgePalm.combinedMass', 'GoodEdgePositivePalm.mass')))

    def test_uniform_s_cannot_be_fixed_before_threshold(self):
        self.type_change_fails('PaperP1.UniformFullSupportCount.companion_T13_1',
                               lambda row: row.update(type='∀ (s : ℕ), ' + row['type']))

    def test_factorial_quotient_is_required(self):
        self.type_change_fails('PaperP1.UniformFullSupportCount.companion_T13_1',
                               lambda row: row.update(type=row['type'].replace('u ^ r / ↑r.factorial', 'u ^ r')))

    def test_saturated_count_has_an_epsilon_margin(self):
        self.type_change_fails('PaperP1.UniformFullSupportCount.companion_T13_1',
                               lambda row: row.update(type=row['type'].replace('-Min.min (↑s / 2) 2 + ε', '-Min.min (↑s / 2) 2')))

    def test_growing_arity_factor_cannot_be_absorbed(self):
        self.type_change_fails('PaperP1.V2HomogeneousEnvelope.uniform_nominal_comparison',
                               lambda row: row.update(type=row['type'].replace('2 ^ I.card * ', '')))

    def test_ordered_centered_clause_is_required(self):
        self.type_change_fails('PaperP1.SharpOrderedPrimitiveMass.companion_T4_7',
                               lambda row: row.update(type=row['type'].replace('infiniteCenteredCoefficient', 'infiniteJointMoment')))

    def test_independent_tail_retains_pure_subcritical_power(self):
        self.type_change_fails('PaperP1.FixedCutoffIndependentTail.uniform_tail',
                               lambda row: row.update(type=row['type'].replace('↑N ^ (-a)', '↑N ^ (-a + ε)')))

    def test_seed_interface_must_retain_both_sharp_rates(self):
        self.type_change_fails('PaperP1.V2FixedHomogeneousSeeds.companion_T1_12',
                               lambda row: row.update(type=row['type'].replace('-41 / 30 + ε', '-4 / 3 + ε')))

    def test_a_definition_is_not_theorem_evidence(self):
        self.type_change_fails('PaperP1.V2HomogeneousEnvelope.finite_domination',
                               lambda row: row.update(kind='definition'))


if __name__ == '__main__':
    unittest.main()
