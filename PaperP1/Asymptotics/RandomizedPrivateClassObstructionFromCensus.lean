module

public import PaperP1.Asymptotics.RandomizedPrivateClassCostFromCensus
public import PaperP1.Asymptotics.OrdinaryCensusNormalization

/-! # The actual randomized half-factor obstruction from the independent source census -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedPrivateClassObstructionFromCensus

open PaperP1.Arithmetic PaperP1.Model PaperP1.RandomizedHybridField
  PaperP1.OrdinarySmoothSourcePopulation PaperP1.LogFifthPivotCutoff PaperP1.AnchoredCostErrorScale

theorem uniform_census_implication (D a t : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1 / 10) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ B Y K M : ℕ,
      1 ≤ K → K + 1 ≤ B → B ≤ Y → Y ≤ cutoff N → (B : ℝ) ≤ D * Real.log N → 2 * N + B ≤ M →
      ((missingCandidates N K ((N : ℝ) ^ a)).card : ℝ) ≤ (t / 2) * N →
      ∀ anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y → Fin (K + 1),
      ∀ A : Data M Y K (PaperP1.AnchoredDyadicField.retainedBoundaries N B Y)
        (PaperP1.RandomizedDyadicHybridField.fullGood N B (cutoff N)) anchor,
      ∀ (Ξ : Type*) [Fintype Ξ], ∀ P : PaperP1.Probability.FiniteProbability Ξ,
      ∀ b : Fin (K + 1) → F₂,
      ∀ g : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y → (Fin (K + 1) → F₂) → Ξ → F₂,
      ∀ F : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y → SampleSpace M × Ξ → SampleSpace M × Ξ,
      PaperP1.RandomizedPrivateForcingClass.AgreesOnGood A b g F →
      (1 - 3 * t) * (PaperP1.AnchoredPrivateField.rate K) ^ 2 / 2 * (N : ℝ) ^ (2 - a) ≤ PaperP1.PositiveForcingCostLower.offsite Finset.univ (law (M := M) P) (indicator b) F := by
  obtain ⟨NN, hNorm⟩ := PaperP1.OrdinaryCensusNormalization.uniform_normalized_ledger D a t hD ha ha1 ht ht1
  obtain ⟨NC, hCost⟩ := PaperP1.RandomizedPrivateClassCostFromCensus.uniform_ordinary_candidates_lower
    D hD (errorExponent a) (errorExponent_pos ha1)
  refine ⟨max NN NC, ?_⟩
  intro N hN B Y K M hK hKB hBY hYZ hB hM hmissing anchor A Ξ _ P b g F hF
  obtain ⟨hnorm, hcollision, hupper, _h2B⟩ := hNorm N (by omega) B K hKB hB hmissing
  have hc := hCost N (by omega) B Y (cutoff N) K M ((N : ℝ) ^ a)
    hK hKB hBY hB hYZ hupper hM hcollision anchor A Ξ P b g F hF
  calc
    _ = ((PaperP1.AnchoredPrivateField.rate K) ^ 2 / 2) * ((1 - 3 * t) * (N : ℝ) ^ (2 - a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity :
      (0 : ℝ) ≤ (PaperP1.AnchoredPrivateField.rate K) ^ 2 / 2)
    _ ≤ PaperP1.PositiveForcingCostLower.offsite Finset.univ (law (M := M) P) (indicator b) F := hc

end PaperP1.RandomizedPrivateClassObstructionFromCensus
