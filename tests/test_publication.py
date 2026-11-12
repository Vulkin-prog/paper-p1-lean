"""Negative controls for the publication correspondence and held Palomar scope."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest

import yaml

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_publication import (check_partition, check_types, check_metadata,
                               check_caller, check_stage)


def read(name):
    return json.loads((ROOT / name).read_text())


class PublicationScope(unittest.TestCase):
    def setUp(self):
        self.index = read('docs/manuscript-results-publication-2026-11-12.json')
        self.prior = read('docs/manuscript-results-v2.0.json')
        self.types = read('docs/validation/publication-2026-11-12/lean-scope/compiled-types.json')
        self.prior_types = read('docs/validation/v2.0/v2-scope/compiled-types.json')
        self.plan = read('palomar/REGISTRATION_PLAN_PUBLICATION.json')
        self.alignment = read('palomar/publication/ALIGNMENT.json')
        self.metadata = yaml.safe_load((ROOT / self.plan['bundles'][0]['metadata']).read_text())
        self.caller = yaml.load((ROOT / '.github/workflows/palomar-publication-preflight.yml').read_text(),
                                Loader=yaml.BaseLoader)

    def test_actual_scope_types_metadata_caller_and_hold(self):
        check_partition(self.index, self.prior)
        check_types(self.types, self.prior_types)
        check_metadata(self.metadata, self.plan['bundles'][0]['slug'])
        check_caller(self.caller, self.plan)
        check_stage(self.alignment)

    def test_missing_result_rejected(self):
        self.index['results'].pop()
        with self.assertRaises(ValueError):
            check_partition(self.index, self.prior)

    def test_replaced_proof_endpoint_rejected(self):
        self.index['results'][0]['entry_points'] = []
        with self.assertRaises(ValueError):
            check_partition(self.index, self.prior)

    def test_changed_main_statement_rejected(self):
        row = next(r for r in self.index['results'] if r['document'] == 'main')
        row['source']['statement_sha256'] = '0' * 64
        row['comparison_to_v2'] = 'clarified_original_contact_scope'
        with self.assertRaises(ValueError):
            check_partition(self.index, self.prior)

    def test_discarded_conditional_premise_rejected(self):
        row = self.index['results'][0]
        row['printed_conditional_clause'] = not row['printed_conditional_clause']
        with self.assertRaises(ValueError):
            check_partition(self.index, self.prior)

    def test_hidden_t43_clarification_rejected(self):
        row = next(r for r in self.index['results'] if r['label'] == 'p1:fixed:propagation')
        row['comparison_to_v2'] = 'identical_statement'
        with self.assertRaises(ValueError):
            check_partition(self.index, self.prior)

    def test_changed_compiled_type_rejected(self):
        self.types[0]['kind'] = 'definition'
        with self.assertRaises(ValueError):
            check_types(self.types, self.prior_types)

    def test_matching_non_proof_records_rejected(self):
        self.types[0]['is_proposition'] = False
        with self.assertRaises(ValueError):
            check_types(self.types, deepcopy(self.types))

    def test_orcid_required_in_all_person_roles(self):
        for role in ['authors', 'responsible_maintainers', 'source']:
            with self.subTest(role=role):
                data = deepcopy(self.metadata)
                person = data['sources'][0]['authors'][0] if role == 'source' else data['project'][role][0]
                person.pop('orcid')
                with self.assertRaises(ValueError):
                    check_metadata(data, 'unused')

    def test_wrong_source_edition_rejected(self):
        self.metadata['sources'][0]['id'] = self.metadata['sources'][0]['id'].replace('publication-2026-11-12', 'v2.0')
        with self.assertRaises(ValueError):
            check_metadata(self.metadata, 'unused')

    def test_unfrozen_metadata_rejected_when_snapshot_required(self):
        self.metadata['sources'][0]['id'] = 'https://github.com/Vulkin-prog/paper-p1-lean/tree/main/manuscripts/paper-p1/publication-2026-11-12'
        with self.assertRaises(ValueError):
            check_metadata(self.metadata, 'unused', 'a' * 40)

    def test_seventh_candidate_rejected(self):
        self.caller['on']['workflow_dispatch']['inputs']['bundle']['options'].append('seventh')
        with self.assertRaises(ValueError):
            check_caller(self.caller, self.plan)

    def test_automatic_preflight_trigger_rejected(self):
        self.caller['on']['push'] = {}
        with self.assertRaises(ValueError):
            check_caller(self.caller, self.plan)

    def test_missing_personal_declaration_rejected(self):
        self.caller['on']['workflow_dispatch']['inputs']['authorization_relationship']['required'] = 'false'
        with self.assertRaises(ValueError):
            check_caller(self.caller, self.plan)

    def test_partial_preflight_or_different_pin_rejected(self):
        for key, value in [('mode', 'partial'), ('pipeline_commit', 'main')]:
            with self.subTest(key=key):
                caller = deepcopy(self.caller)
                caller['jobs']['verify']['with'][key] = value
                with self.assertRaises(ValueError):
                    check_caller(caller, self.plan)

    def test_parallel_submission_group_rejected(self):
        self.caller['concurrency']['group'] = 'different-group'
        with self.assertRaises(ValueError):
            check_caller(self.caller, self.plan)

    def test_unfounded_official_stage_rejected(self):
        for key, value in [('author_submission_hold', False),
                           ('official_full_preflight_passed', True),
                           ('intake_started', True), ('registration', 'invented-id'),
                           ('new_kernel_suite_performed', True)]:
            with self.subTest(key=key):
                alignment = deepcopy(self.alignment)
                alignment[key] = value
                with self.assertRaises(ValueError):
                    check_stage(alignment)


if __name__ == '__main__':
    unittest.main()
