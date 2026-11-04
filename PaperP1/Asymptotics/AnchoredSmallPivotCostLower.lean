module

public import PaperP1.Asymptotics.AnchoredDyadicCostLower
public import PaperP1.Model.AnchoredSmallPivotSelection
public import PaperP1.Analysis.CleanPairReciprocalLower

/-! # The actual anchored offsite lower bound from the ordinary-candidate census

The count of good ordinary-candidate sources remains literal. Small
nonanchor source pivots are selected internally for every anchor rule;
no reciprocal lower bound or assumed forcing cost is a theorem premise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredSmallPivotCostLower

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ForcingExceptionalSets
  PaperP1.AnchoredPrivateValues PaperP1.AnchoredPrivateField
  PaperP1.AnchoredSmallPivotSelection PaperP1.OrdinarySmoothSourcePopulation
  PaperP1.AnchoredCleanBoundaryPairs PaperP1.CleanPivotPairs

theorem uniform_ordinary_candidates_lower (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ B Y Z K M : ℕ, ∀ Q : ℝ,
      1 ≤ K → K + 1 ≤ B → B ≤ Y → (B : ℝ) ≤ D * Real.log N →
      Y ≤ Z → (Z : ℝ) ≤ (Real.log N) ^ 5 → 2 * N + B ≤ M →
      ((K : ℝ) * (K + 1 : ℕ) + 1) ≤ Z →
      ∀ anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y → Fin (K + 1),
      ∀ A : Data M Y K (PaperP1.AnchoredDyadicField.retainedBoundaries N B Y) anchor,
      ∀ b : Fin (K + 1) → F₂,
      (rate K) ^ 2 *
        ((1 - ((K : ℝ) * (K + 1 : ℕ) + 1) / Z) * N *
            ((goodSources N K B Z Q).card / Q) -
          (((K : ℝ) * (K + 1 : ℕ) + 1) + 1) * (goodSources N K B Z Q).card -
          (N : ℝ) ^ (19 / 10 + ε : ℝ) - (N : ℝ) ^ (3 / 2 + ε : ℝ)) ≤ offsite A b := by
  obtain ⟨NE, hE⟩ := PaperP1.AnchoredDyadicCostLower.uniform_actual_offsite_lower D hD ε hε
  refine ⟨NE, ?_⟩
  intro N hN B Y Z K M Q hK hKB hBY hB hYZ hZ hM hcollision anchor A b
  have hn : 2 ≤ N := by omega
  obtain ⟨selected, hselected⟩ := exists_actual_small_selector Q hn hK hYZ anchor A
  let J := goodSources N K B Z Q
  have hJ : J ⊆ PaperP1.AnchoredDyadicField.retainedBoundaries N B Y :=
    goodSources_subset_retained Q hn hYZ
  have hgood : ∀ j ∈ J, j ∉ badBoundaries N B Z := fun _ hj ↦ (mem_goodSources.mp hj).2.2
  have hoff := hE N hN B Y Z K M hK hKB hBY hB hYZ hZ hM anchor A selected b J hJ hgood
  have hrec := reciprocal_source_lower A selected J Q hselected
  have hz : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  have hf := PaperP1.CleanPairReciprocalLower.substitute_lower
    (n := (N : ℝ)) (s := reciprocalSum J (selectedPrime A selected)) (j := (J.card : ℝ))
    (c := (K : ℝ) * (K + 1 : ℕ) + 1) (z := (Z : ℝ)) (Q := Q)
    (Nat.cast_nonneg N) hz hcollision hrec
  have herr := sub_le_sub_right (sub_le_sub_right hf ((N : ℝ) ^ (19 / 10 + ε : ℝ)))
    ((N : ℝ) ^ (3 / 2 + ε : ℝ))
  exact (mul_le_mul_of_nonneg_left herr (sq_nonneg (rate K))).trans hoff

end PaperP1.AnchoredSmallPivotCostLower
