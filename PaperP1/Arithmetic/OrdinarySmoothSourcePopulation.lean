module

public import PaperP1.Arithmetic.NonanchorPivotSelection
public import PaperP1.Model.ForcingExceptionalSets

/-! # Exact source population after ordinary-candidate and pivot exclusions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinarySmoothSourcePopulation

open Finset PaperP1.NonanchorPivotSelection PaperP1.ForcingExceptionalSets

local instance ordinarySmoothSourceDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def goodSources (N K B Z : ℕ) (Q : ℝ) : Finset ℕ :=
  ((boundaryBlock N).filter fun j ↦ 2 ≤ (ordinaryIndices j (K + 1) Q).card) \ badBoundaries N B Z

def missingCandidates (N K : ℕ) (Q : ℝ) : Finset ℕ :=
  (boundaryBlock N).filter fun j ↦ (ordinaryIndices j (K + 1) Q).card < 2

theorem mem_goodSources {N K B Z j : ℕ} {Q : ℝ} :
    j ∈ goodSources N K B Z Q ↔ j ∈ boundaryBlock N ∧
      2 ≤ (ordinaryIndices j (K + 1) Q).card ∧ j ∉ badBoundaries N B Z := by
  simp only [goodSources, mem_sdiff, mem_filter, and_assoc]

theorem goodSources_subset (N K B Z : ℕ) (Q : ℝ) : goodSources N K B Z Q ⊆ boundaryBlock N :=
  fun _ hj ↦ (mem_goodSources.mp hj).1

theorem source_deletion_ledger {N K B Z : ℕ} (Q : ℝ) (hN : 2 ≤ N) :
    N ≤ (goodSources N K B Z Q).card + (missingCandidates N K Q).card +
      (badBoundaries N B Z).card := by
  have hc : boundaryBlock N ⊆ goodSources N K B Z Q ∪
      (missingCandidates N K Q ∪ badBoundaries N B Z) := by
    intro j hj
    by_cases hb : j ∈ badBoundaries N B Z
    · exact mem_union_right _ (mem_union_right _ hb)
    · by_cases hs : 2 ≤ (ordinaryIndices j (K + 1) Q).card
      · exact mem_union_left _ (mem_goodSources.mpr ⟨hj, hs, hb⟩)
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hj, by omega⟩))
  have h := (card_le_card hc).trans (card_union_le _ _)
  have hu := card_union_le (missingCandidates N K Q) (badBoundaries N B Z)
  rw [boundaryBlock_card hN] at h
  omega

end PaperP1.OrdinarySmoothSourcePopulation
