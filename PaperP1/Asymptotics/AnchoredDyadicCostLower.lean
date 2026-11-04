module

public import PaperP1.Model.AnchoredCleanSourceData
public import PaperP1.Asymptotics.ForcingExceptionLedger

/-! # Actual offsite anchored forcing cost with all exceptional losses proved

The rule and selected nonanchor prime are deterministic functions on the
integer source population. The reciprocal source sum remains literal;
no abundance of ordinary smooth source values is assumed or claimed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredDyadicCostLower

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ForcingExceptionalSets
  PaperP1.AnchoredPrivateValues PaperP1.AnchoredPrivateField PaperP1.AnchoredCleanBoundaryPairs
  PaperP1.AnchoredCleanSourceData PaperP1.CleanPivotPairs

theorem uniform_actual_offsite_lower (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ B Y Z K M : ℕ,
      1 ≤ K → K + 1 ≤ B → B ≤ Y → (B : ℝ) ≤ D * Real.log N →
      Y ≤ Z → (Z : ℝ) ≤ (Real.log N) ^ 5 → 2 * N + B ≤ M →
      ∀ anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y → Fin (K + 1),
      ∀ A : Data M Y K (PaperP1.AnchoredDyadicField.retainedBoundaries N B Y) anchor,
      ∀ selected : ∀ j : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y, Free (anchor j),
      ∀ b : Fin (K + 1) → F₂, ∀ J : Finset ℕ,
      J ⊆ PaperP1.AnchoredDyadicField.retainedBoundaries N B Y →
      (∀ j ∈ J, j ∉ badBoundaries N B Z) →
      (rate K) ^ 2 *
        ((N : ℝ) * reciprocalSum J (selectedPrime A selected) - J.card -
          ((K : ℝ) * (K + 1 : ℕ) + 1) *
            (((N : ℝ) / Z) * reciprocalSum J (selectedPrime A selected) + J.card) -
          (N : ℝ) ^ (19 / 10 + ε : ℝ) - (N : ℝ) ^ (3 / 2 + ε : ℝ)) ≤ offsite A b := by
  obtain ⟨NE, hE⟩ := PaperP1.ForcingExceptionLedger.uniform_surviving_lower D hD ε hε
  refine ⟨NE, ?_⟩
  intro N hN B Y Z K M hK hKB hBY hB hYZ hZ hM anchor A selected b J hJ hgood
  have hn : 2 ≤ N := by omega
  have hG := PaperP1.AnchoredDyadicField.retained_subset N B Y
  have hretain : ∀ n ∈ boundaryBlock N, n ∉ badBoundaries N B Z →
      n ∈ PaperP1.AnchoredDyadicField.retainedBoundaries N B Y :=
    fun _ hnB hbad ↦ PaperP1.AnchoredDyadicField.retained_of_not_bad hn hYZ hnB hbad
  have hq : ∀ j ∈ J, Z ≤ selectedPrime A selected j := by
    intro j hj
    exact (source_conditions A selected hn hKB hG ⟨j, hJ hj⟩ (hgood j hj)).1
  have hr : ∀ j ∈ J, ∀ r ∈ otherPrimes A selected j, Z ≤ r := by
    intro j hj
    exact (source_conditions A selected hn hKB hG ⟨j, hJ hj⟩ (hgood j hj)).2.1
  have hcop : ∀ j ∈ J, ∀ r ∈ otherPrimes A selected j, (selectedPrime A selected j).Coprime r := by
    intro j hj
    exact (source_conditions A selected hn hKB hG ⟨j, hJ hj⟩ (hgood j hj)).2.2.1
  have hsize : ∀ j ∈ J, (otherPrimes A selected j).card ≤ K := by
    intro j hj
    exact (source_conditions A selected hn hKB hG ⟨j, hJ hj⟩ (hgood j hj)).2.2.2
  have hl := hE N (by omega) B Z M (K + 1) (K + 1) K (by omega) hB (by omega) hZ
    hM hKB hKB J (hJ.trans hG) (selectedPrime A selected) (otherPrimes A selected) hq hr hcop hsize
  have hw := mul_le_mul_of_nonneg_left hl (sq_nonneg (rate K))
  exact hw.trans (actual_offsite_lower A hK b selected hn hG hretain hJ)

end PaperP1.AnchoredDyadicCostLower
