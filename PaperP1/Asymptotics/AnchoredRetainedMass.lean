module

public import PaperP1.Model.AnchoredDyadicField
public import PaperP1.Asymptotics.PolylogPivotCount

/-! # Uniform retained unsigned mass for every admissible arithmetic anchor

The strict all-good population is contained in the original at-most-one
small-pivot population. Its proved Rankin loss controls the true total
mean uniformly over all anchor rules and both unsigned templates.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredRetainedMass

open PaperP1.Arithmetic PaperP1.Model PaperP1.AnchoredDyadicField PaperP1.AnchoredPrivateField
  PaperP1.ForcingExceptionalSets PaperP1.Probability PaperP1.UniformFubini

theorem uniform_total_mean (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, max N₀ 2 ≤ N → ∀ B Y Z K M : ℕ,
      (B : ℝ) ≤ D * Real.log N → Y ≤ Z → 1 ≤ Z → (Z : ℝ) ≤ (Real.log N) ^ 5 →
      ∀ anchor : retainedBoundaries N B Y → Fin (K + 1),
      Data M Y K (retainedBoundaries N B Y) anchor → ∀ b : Fin (K + 1) → F₂,
      ((N : ℝ) - (N : ℝ) ^ (9 / 10 + ε : ℝ)) * rate K ≤
        (∑ j : retainedBoundaries N B Y, exactMarginal (cylinderProbability M) (indicator b) j) ∧
      (∑ j : retainedBoundaries N B Y, exactMarginal (cylinderProbability M) (indicator b) j) ≤
        (N : ℝ) * rate K := by
  obtain ⟨NV, hV⟩ := PaperP1.PolylogPivotCount.uniform_window_bound D hD ε hε
  refine ⟨NV, ?_⟩
  intro N hN B Y Z K M hB hYZ hZ hcut anchor A b
  have hn : 2 ≤ N := by omega
  have hv := hV N (by omega) B Z hB hZ hcut
  have hc : ((badBoundaries N B Z).card : ℝ) ≤
      (PaperP1.PolylogPivotExceptions.badWindows N B Z).card := by
    exact_mod_cast badBoundaries_card_le N B Z
  have hl : (N : ℝ) ≤ (retainedBoundaries N B Y).card + (badBoundaries N B Z).card := by
    exact_mod_cast retention_ledger (B := B) hn hYZ
  have hu : ((retainedBoundaries N B Y).card : ℝ) ≤ N := by exact_mod_cast retained_card_le N B Y
  rw [total_marginal A]
  constructor
  · apply mul_le_mul_of_nonneg_right _ (rate_pos K).le
    linarith only [hl, hc, hv]
  · exact mul_le_mul_of_nonneg_right hu (rate_pos K).le

end PaperP1.AnchoredRetainedMass
