module

public import PaperP1.Algebra.ThreeFiniteValueSpan
public import PaperP1.Model.NormalizedFamilyDefectRank

/-! # Three normalized windows retain the whole value-kernel defect without any overlap assumption -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeNormalizedFamilyRank

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NormalizedWindowSets
  PaperP1.PrivateNormalizedFamilies

theorem joint_space_three (X : Fin 3 → ℕ) (L : ℕ) :
    (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) =
      (squareClassSpace (X 0) L ⊔ squareClassSpace (X 1) L) ⊔ squareClassSpace (X 2) L := by
  apply le_antisymm
  · apply iSup_le
    intro i
    fin_cases i
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  · exact sup_le (sup_le (le_iSup (fun i ↦ squareClassSpace (X i) L) 0)
      (le_iSup (fun i ↦ squareClassSpace (X i) L) 1)) (le_iSup (fun i ↦ squareClassSpace (X i) L) 2)

theorem union_three (c X : Fin 3 → ℕ) (L : ℕ) : valueUnion c X L =
    (normalized (c 0) (X 0) L ∪ normalized (c 1) (X 1) L) ∪ normalized (c 2) (X 2) L := by
  have hu : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [valueUnion, hu]
  simp only [biUnion_insert, singleton_biUnion]
  exact union_assoc _ _ _ |>.symm

theorem card_le_rank_add_kernel {L : ℕ} (c X : Fin 3 → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) :
    (valueUnion c X L).card ≤
      Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) +
        Module.finrank F₂ (FiniteResidualRank.valueKernel (valueUnion c X L)) + 3 := by
  have hfull := ThreeFiniteValueSpan.full_union_rank_le_three_even_add_three (K := F₂) parityVec
    (normalized (c 0) (X 0) L) (normalized (c 1) (X 1) L) (normalized (c 2) (X 2) L)
    (normalized_nonempty _ _ _) (normalized_nonempty _ _ _) (normalized_nonempty _ _ _)
  change Module.finrank F₂ (FiniteSetValueSpan.span (K := F₂) parityVec
    ((normalized (c 0) (X 0) L ∪ normalized (c 1) (X 1) L) ∪ normalized (c 2) (X 2) L)) ≤
      Module.finrank F₂ ↥((FiniteEvenSquareClasses.space (normalized (c 0) (X 0) L) ⊔
        FiniteEvenSquareClasses.space (normalized (c 1) (X 1) L)) ⊔
        FiniteEvenSquareClasses.space (normalized (c 2) (X 2) L)) + 3 at hfull
  rw [← union_three c X L, space_normalized (hc 0) (hX 0), space_normalized (hc 1) (hX 1),
    space_normalized (hc 2) (hX 2), ← joint_space_three] at hfull
  have heq := FiniteSetValueSpan.rank_add_kernel (K := F₂) parityVec (valueUnion c X L)
  change Module.finrank F₂ (FiniteSetValueSpan.span (K := F₂) parityVec (valueUnion c X L)) +
    Module.finrank F₂ (FiniteResidualRank.valueKernel (valueUnion c X L)) = (valueUnion c X L).card at heq
  omega

end PaperP1.ThreeNormalizedFamilyRank
