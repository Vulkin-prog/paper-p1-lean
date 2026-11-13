"""Controls against false completeness, changed scope and wrong public evidence."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import check_registered_coverage as audit


class RegisteredCoverageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.plan = audit.load(ROOT, audit.PLAN)
        cls.index = audit.load(ROOT, cls.plan['source_index'])
        cls.state = audit.load(ROOT, audit.STATE)
        cls.cycle = next(item for item in cls.state['cycles'] if item['slug'] == 'stopping_reconstruction')
        cls.bundle = next(item for item in cls.plan['bundles'] if item['slug'] == cls.cycle['slug'])
        receipt = audit.load(ROOT, cls.cycle['registration']['public_data_receipt'])
        cls.entry = audit.load(ROOT, receipt['entry_path'])
        cls.versions = json.loads((ROOT / receipt['entry_path']).with_name('versions.json').read_text())
        cls.config = json.loads(audit.committed(str(ROOT), cls.cycle['source_commit'], cls.bundle['configuration']))

    def check_entry(self, entry, cycle=None):
        audit.validate_public_entry(entry, self.versions, cycle or self.cycle, self.bundle, self.config)

    def test_actual_public_record_accepts_registry_orcid_check_timestamp(self):
        self.assertIn('orcid_record_checked_at', self.entry['authors'][0])
        self.check_entry(self.entry)

    def test_actual_allocation_preserves_auxiliary_selections(self):
        audit.validate_allocation(self.plan, self.index)
        mapped = {name for b in self.plan['bundles'] for item in b['main_results']
                  for name in item['selected_declarations']}
        self.assertEqual(sum(len(b['selected_declarations']) for b in self.plan['bundles']), 52)
        self.assertEqual(len(mapped), 47)

    def test_changed_source_is_refused(self):
        cycle = copy.deepcopy(self.cycle)
        cycle['source_commit'] = '0' * 40
        with self.assertRaisesRegex(ValueError, 'registered source'):
            self.check_entry(self.entry, cycle)

    def test_orcid_in_mathematical_source_must_match(self):
        entry = copy.deepcopy(self.entry)
        source = next(item for item in entry['provenance']['mathematical_sources']
                      if item.get('relationship') == 'formalizes')
        source['authors'][0]['orcid'] = '0000-0000-0000-0000'
        with self.assertRaisesRegex(ValueError, 'ORCID'):
            self.check_entry(entry)

    def test_missing_registered_declaration_is_refused(self):
        entry = copy.deepcopy(self.entry)
        entry['formalization']['theorem_names'].pop()
        with self.assertRaisesRegex(ValueError, 'selection differs'):
            self.check_entry(entry)

    def test_unissued_record_is_not_counted(self):
        entry = copy.deepcopy(self.entry)
        entry['status'] = 'pending'
        with self.assertRaisesRegex(ValueError, 'issued public'):
            self.check_entry(entry)

    def test_uncovered_main_result_is_refused(self):
        plan = copy.deepcopy(self.plan)
        plan['bundles'][0]['main_results'].pop()
        with self.assertRaisesRegex(ValueError, 'covered exactly once'):
            audit.validate_allocation(plan, self.index)

    def test_printed_conditional_premise_cannot_be_erased(self):
        plan = copy.deepcopy(self.plan)
        result = next(item for b in plan['bundles'] for item in b['main_results'] if item['number'] == '5.2')
        result['printed_conditional_clause'] = False
        with self.assertRaisesRegex(ValueError, 'conditional scope'):
            audit.validate_allocation(plan, self.index)

    def test_altered_archived_report_bytes_are_refused(self):
        receipt = audit.load(ROOT, self.cycle['preflight']['validation_receipt'])
        with tempfile.TemporaryDirectory(prefix='p1-public-evidence-') as temporary:
            root = Path(temporary)
            (root / 'receipt.json').write_text(json.dumps(receipt))
            report = root / receipt['report_path']
            report.parent.mkdir(parents=True)
            report.write_bytes(audit.local(ROOT, receipt['report_path']).read_bytes() + b' ')
            cycle = copy.deepcopy(self.cycle)
            cycle['preflight']['validation_receipt'] = 'receipt.json'
            with self.assertRaisesRegex(ValueError, 'report bytes changed'):
                audit.mechanical_evidence(root, cycle, 'preflight', 'palomar-standard-v1')

    def test_shared_source_and_equal_count_do_not_identify_renderer(self):
        receipt = audit.load(ROOT, self.cycle['palomar_rendering']['validation_receipt'])
        report = copy.deepcopy(audit.load(ROOT, receipt['report_path']))
        report['source']['comparator_config_path'] = 'RegistryV2/comparator/p1_cumulants_optimality.json'
        with self.assertRaisesRegex(ValueError, 'Another rendered dossier'):
            audit.validate_render_report(ROOT, report, receipt, self.cycle, self.bundle, self.config)

    def test_actual_archive_prefix_counts_only_issued_entries(self):
        report = audit.inspect(ROOT)
        completed = [item for item in self.state['cycles'] if item.get('registration')]
        self.assertEqual(report['registered_dossiers'], len(completed))
        self.assertEqual(report['registered_selected_declarations'],
                         sum(item['selected_theorem_count'] for item in completed))
        self.assertEqual(sum(item['registered'] for item in report['main_results']), report['registered_main_results'])
        self.assertTrue(next(item for item in report['main_results'] if item['number'] == '5.2')['printed_conditional_clause'])

    def test_prepared_dossiers_cannot_satisfy_complete_registration(self):
        state = copy.deepcopy(self.state)
        for cycle in state['cycles'][3:]:
            cycle['registration'] = None
        state['registered_count'] = 3
        original_load = audit.load
        def read(root, path):
            return state if path == audit.STATE else original_load(root, path)
        with patch.object(audit, 'load', side_effect=read):
            with self.assertRaisesRegex(ValueError, 'Six public registrations are not complete'):
                audit.inspect(ROOT, require_all=True)


if __name__ == '__main__':
    unittest.main()
