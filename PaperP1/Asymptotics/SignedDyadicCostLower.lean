module

public import PaperP1.Model.SignedCleanSourceData
public import PaperP1.Asymptotics.ForcingExceptionLedger

/-! # A uniform actual signed forcing cost minorant with proved arithmetic losses

This is an inequality for the original specified dyadic Palm forcing.
Its reciprocal source sum is kept exact. No sharp reciprocal asymptotic
or claimed logarithmic cost equivalent is assumed in the theorem.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedDyadicCostLower

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.OddPrimePivot
  PaperP1.SignedDyadicCleanPairs PaperP1.SignedCleanSourceData
  PaperP1.SignedPrivateDyadicField PaperP1.SignedExactWords
  PaperP1.ForcingExceptionalSets PaperP1.CleanPivotPairs

theorem uniform_actual_lower (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, ∀ hN : max N₀ 2 ≤ N, ∀ L E Y : ℕ, ∀ hL : 1 ≤ L,
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N →
      pivotCutoff L E ≤ Y → (Y : ℝ) ≤ (Real.log N) ^ 5 →
      ∀ J : Finset ℕ, J ⊆ boundaryBlock N →
      (∀ j ∈ J, j ∉ badBoundaries N (L + E + 2) Y) →
      (signedMarkRate L 0) ^ 2 *
        ((N : ℝ) * reciprocalSum J largestOddPrime - J.card -
          (((L + 1 : ℕ) : ℝ) * (L + 2 : ℕ) + 1) *
            (((N : ℝ) / Y) * reciprocalSum J largestOddPrime + J.card) -
          (N : ℝ) ^ (19 / 10 + ε : ℝ) - (N : ℝ) ^ (3 / 2 + ε : ℝ)) ≤
        PaperP1.SignedPrivateField.cost (data (E := E) (by omega : 2 ≤ N) hL) := by
  obtain ⟨NE, hE⟩ := PaperP1.ForcingExceptionLedger.uniform_surviving_lower D hD ε hε
  refine ⟨NE, ?_⟩
  intro N hN L E Y hL hwidth hY hcut J hJ hgood
  have hn : 2 ≤ N := by omega
  have hy : L + 2 ≤ Y := by have := hY; unfold pivotCutoff at this; omega
  have hq : ∀ j ∈ J, Y ≤ largestOddPrime j := fun j hj ↦
    (source_conditions hn hy (hJ hj) (hgood j hj)).1
  have hr : ∀ j ∈ J, ∀ r ∈ otherPivots L j, Y ≤ r := fun j hj ↦
    (source_conditions hn hy (hJ hj) (hgood j hj)).2.1
  have hcop : ∀ j ∈ J, ∀ r ∈ otherPivots L j, (largestOddPrime j).Coprime r := fun j hj ↦
    (source_conditions hn hy (hJ hj) (hgood j hj)).2.2
  have hsize : ∀ j ∈ J, (otherPivots L j).card ≤ L + 1 := fun j _ ↦ otherPivots_card L j
  have hl := hE N (by omega) (L + E + 2) Y (cylinderCutoff N L E)
    (L + 2) (L + 2) (L + 1) (by omega) hwidth (by omega) hcut
    le_rfl (by omega) (by omega) J hJ largestOddPrime (otherPivots L) hq hr hcop hsize
  have hw := mul_le_mul_of_nonneg_left hl (sq_nonneg (signedMarkRate L 0))
  have hc := actual_cost_lower hn hL hY hJ hgood (0 : F₂)
  exact hw.trans hc

end PaperP1.SignedDyadicCostLower
