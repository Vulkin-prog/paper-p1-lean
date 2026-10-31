module

public import PaperP1.Coding.WindowRelationCode

/-! # A nonzero even relation needs two actual defective vertices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoDefectsInRelation

open PaperP1.Arithmetic WindowRelationCode DefectivePredicate Finset

local instance twoDefectsRelationPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem nonzero_relation_has_two_defects {U B : ℕ}
    (w : windowRelationCode U B) (hw : w ≠ 0) :
    ∃ i j : Fin B, i ≠ j ∧ HDefective B (U + i.val) ∧ HDefective B (U + j.val) := by
  classical
  have hi : ∃ i : Fin B, (w : Fin B → F₂) i ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    apply Subtype.ext
    exact funext h
  obtain ⟨i, hi⟩ := hi
  have hj : ∃ j : Fin B, j ≠ i ∧ (w : Fin B → F₂) j ≠ 0 := by
    by_contra h
    push Not at h
    have hsum : (∑ j, (w : Fin B → F₂) j) = (w : Fin B → F₂) i := by
      exact sum_eq_single i (fun j _ hji ↦ h j hji) (by simp)
    have heven := ((mem_windowRelationCode _).mp w.property).2
    exact hi (hsum.symm.trans heven)
  obtain ⟨j, hji, hj⟩ := hj
  refine ⟨i, j, hji.symm, ?_, ?_⟩
  · by_contra h
    exact hi (coefficient_zero_of_mem w i h)
  · by_contra h
    exact hj (coefficient_zero_of_mem w j h)

theorem relation_eq_bot_of_at_most_one_defect {U B : ℕ}
    (h : ∀ i j : Fin B, HDefective B (U + i.val) →
      HDefective B (U + j.val) → i = j) : windowRelationCode U B = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro w hw
  by_contra hne
  have hne' : (⟨w, hw⟩ : windowRelationCode U B) ≠ 0 := by
    intro heq
    exact hne (congrArg Subtype.val heq)
  obtain ⟨i, j, hij, hi, hj⟩ := nonzero_relation_has_two_defects ⟨w, hw⟩ hne'
  exact hij (h i j hi hj)

end PaperP1.TwoDefectsInRelation
