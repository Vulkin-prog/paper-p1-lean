"""Guard against lost clauses, weakened thresholds and changed issued sources."""
import copy
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import check_registry_final as audit

class RegistryFinalTests(unittest.TestCase):
    def test_actual_candidate_and_preserved_records(self):
        self.assertEqual(audit.check()['inherited_main_clauses'],13)

    def test_missing_inherited_clause_is_refused(self):
        original=audit.read
        def read(path):
            result=original(path)
            if path.name=='clause-map.json':
                result=copy.deepcopy(result);result['inherited_clauses'].pop()
            return result
        with patch.object(audit,'read',side_effect=read):
            with self.assertRaisesRegex(ValueError,'clause was lost'):audit.check()

    def test_fixed_family_cannot_replace_all_subfamilies(self):
        original=Path.read_text
        def read(path,*args,**kwargs):
            result=original(path,*args,**kwargs)
            if path.name=='ChallengeP1FinalFoundations.lean':
                result=result.replace('→ ∀ I : Finset ℕ, I ⊆ Ico N (2*N)',
                                      '→ ∀ I : Finset ℕ, I.card ≤ 254 → I ⊆ Ico N (2*N)')
            return result
        with patch.object(Path,'read_text',read):
            with self.assertRaisesRegex(ValueError,'every inherited clause'):audit.check()

    def test_proof_hole_cannot_count_as_solution(self):
        original=Path.read_text
        def read(path,*args,**kwargs):
            result=original(path,*args,**kwargs)
            if path.name=='SolutionP1FinalFoundations.lean':result+='\ntheorem bad : False := by sorry\n'
            return result
        with patch.object(Path,'read_text',read):
            with self.assertRaisesRegex(ValueError,'Unproved Solution'):audit.check()

    def test_minimum_support_size_cannot_precede_the_threshold(self):
        original=audit.read
        def read(path):
            result=original(path)
            if path.name=='clause-map.json':
                result=copy.deepcopy(result)
                row=result['additional_companion_result']
                row['literal_clause_type']=row['literal_clause_type'].replace(
                    '∃ N₀ : ℕ,','∀ s : ℕ, 2≤s → ∃ N₀ : ℕ,',1)
            return result
        with patch.object(audit,'read',side_effect=read):
            with self.assertRaisesRegex(ValueError,'Uniform count hypothesis or quantifier changed'):audit.check()

    def test_an_issued_file_cannot_be_changed(self):
        original=audit.sha
        def digest(path):
            return '0'*64 if path.name=='ChallengeP1V2AffineEvents.lean' else original(path)
        with patch.object(audit,'sha',side_effect=digest):
            with self.assertRaisesRegex(ValueError,'immutable registered source'):audit.check()

if __name__=='__main__':unittest.main()
