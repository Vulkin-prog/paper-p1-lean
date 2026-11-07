"""Focused in-memory controls for the new strengthened seed clauses and bridges."""
from copy import deepcopy
from pathlib import Path
import json
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import check_unified_preview as guard

def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()

class UnifiedPreviewControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.files = guard.prior.Files()
        cls.final = cls.files.json(guard.PROPOSAL + '/final-validation.json')
        cls.review = cls.files.json(guard.PROPOSAL + '/independent-patch-review.json')

    def test_current_capsule_and_four_prior_capsules_pass(self):
        result = guard.verify()
        self.assertEqual(result['current_targeted_propositions'], 21)
        self.assertEqual(result['source_lines_saved_this_pass'], 51)
        self.assertEqual(result['pages_saved_this_pass'], 0)

    def reject_source_change(self, file, old, new):
        path = guard.PACKAGE + '/sources/' + file
        text = self.files.text(path)
        self.assertEqual(text.count(old), 1)
        with self.assertRaisesRegex(ValueError, 'Delivered unified manuscript differs'):
            guard.verify(guard.prior.Files(overrides={path: text.replace(old, new, 1).encode()}))

    def test_beta_positivity_cannot_be_omitted(self):
        self.reject_source_change('companion_sections/arithmetic.tex',
            r'LN^{-1+1/b}>0$', r'LN^{-1+1/b}$')

    def test_zero_singleton_crossing_case_cannot_be_discarded(self):
        self.reject_source_change('companion_sections/arithmetic_appendix.tex',
            'even when both individual target crossings vanish.', 'only when a target crossing is positive.')

    def test_pure_constant_cannot_acquire_an_epsilon_loss(self):
        self.reject_source_change('companion_sections/arithmetic_appendix.tex',
            ' \\sum_{e\\ne f}W(e\\cup f)\n \\ll_C L^2N^{-4/3}.',
            ' \\sum_{e\\ne f}W(e\\cup f)\n \\ll_{C,\\varepsilon} L^2N^{-4/3+\\varepsilon}.')

    def test_old_weak_seed_alias_cannot_cover_the_new_sharp_clause(self):
        path = guard.PROPOSAL + '/preview-result-map.json'
        data = self.files.json(path)
        row = next(r for r in data['results'] if r['label'] == guard.SEED)
        row['common_seed_entry_points'] = ['PaperP1.FixedHomogeneousSeedTheorem.companion_T1_12']
        with self.assertRaisesRegex(ValueError, 'lacks its actual strong theorem'):
            guard.verify(guard.prior.Files(overrides={path: encoded(data)}))

    def test_old_historical_type_read_cannot_cover_current_twenty_one(self):
        review = deepcopy(self.review)
        review['compiled_entries_read'].pop()
        with self.assertRaisesRegex(ValueError, 'Independent common-seed scope differs'):
            guard.reviewed_scope(self.files, self.final['compiled_scope'], review)

    def test_changed_current_source_requires_a_new_body_read(self):
        row = self.review['compiled_entries_read'][0]
        path = row['file']
        data = self.files.read(path) + b'\n'
        with self.assertRaisesRegex(ValueError, 'Reviewed Lean source changed'):
            guard.reviewed_scope(guard.prior.Files(overrides={path: data}), self.final['compiled_scope'], self.review)

    def test_newer_snapshot_cannot_silently_replace_the_reviewed_source(self):
        review = deepcopy(self.review)
        review['compiled_entries_read'][0]['source_commit'] = '0' * 40
        with self.assertRaisesRegex(ValueError, 'body or proof source differs'):
            guard.reviewed_scope(self.files, self.final['compiled_scope'], review)

if __name__ == '__main__':
    unittest.main()
