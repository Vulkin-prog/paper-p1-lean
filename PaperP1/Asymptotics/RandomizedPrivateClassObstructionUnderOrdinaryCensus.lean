module

public import PaperP1.Asymptotics.RandomizedPrivateClassObstructionFromCensus
public import PaperP1.Asymptotics.AnchoredObstructionUnderOrdinaryCensus

/-! # The randomized part of T19.17 under the independent ordinary source census

This is the actual original-population offsite cost of every allowed private forcing. Its extra
factor 1/2 is proved uniformly for every independent finite auxiliary
law and every source-dependent orientation. Fairness separately
certifies the original-prime conditional law of the hybrid coupling.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedPrivateClassObstructionUnderOrdinaryCensus

open PaperP1.Arithmetic PaperP1.Model PaperP1.RandomizedHybridField
  PaperP1.AnchoredObstructionUnderOrdinaryCensus PaperP1.LogFifthPivotCutoff

theorem randomized_under_census (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1 / 10) (hCensus : OrdinaryCensusDensity C a)
    (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E Y M : ℕ, ∀ i : Fin 2,
      1 ≤ L → L + E + 2 ≤ Y → Y ≤ cutoff N →
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N → 2 * N + (L + E + 2) ≤ M →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) Y → Fin (L + i.val + 1),
      ∀ A : Data M Y (L + i.val) (PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) Y)
        (PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N)) anchor,
      ∀ (Ξ : Type*) [Fintype Ξ], ∀ P : PaperP1.Probability.FiniteProbability Ξ,
      ∀ b : Fin (L + i.val + 1) → F₂,
      ∀ g : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) Y →
        (Fin (L + i.val + 1) → F₂) → Ξ → F₂,
      ∀ F : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) Y →
        SampleSpace M × Ξ → SampleSpace M × Ξ,
      PaperP1.RandomizedPrivateForcingClass.AgreesOnGood A b g F →
      (1 - η) * (PaperP1.AnchoredPrivateField.rate (L + i.val)) ^ 2 / 2 * (N : ℝ) ^ (2 - a) ≤ PaperP1.PositiveForcingCostLower.offsite Finset.univ (law (M := M) P) (indicator b) F := by
  let t : ℝ := min 1 (η / 3)
  have ht : 0 < t := lt_min zero_lt_one (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  obtain ⟨NO, hO⟩ := PaperP1.RandomizedPrivateClassObstructionFromCensus.uniform_census_implication D a t hD ha ha1 ht ht1
  obtain ⟨NM, hM⟩ := hCensus (t / 2) (by positivity)
  refine ⟨max NO NM, ?_⟩
  intro N hN L E Y M i hL hBY hYZ hwidth hcut hband anchor A Ξ _ P b g F hF
  have hival := i.isLt
  have hmissing := hM N (by omega) L i hband
  have hoff := hO N (by omega) (L + E + 2) Y (L + i.val) M (by omega) (by omega)
    hBY hYZ hwidth hcut hmissing anchor A Ξ P b g F hF
  have hco : 1 - η ≤ 1 - 3 * t := by
    have hh : t ≤ η / 3 := min_le_right _ _
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hco
    (by positivity : (0 : ℝ) ≤ (PaperP1.AnchoredPrivateField.rate (L + i.val)) ^ 2 / 2 * (N : ℝ) ^ (2 - a))
  have hm' : (1 - η) * (PaperP1.AnchoredPrivateField.rate (L + i.val)) ^ 2 / 2 * (N : ℝ) ^ (2 - a) ≤
      (1 - 3 * t) * (PaperP1.AnchoredPrivateField.rate (L + i.val)) ^ 2 / 2 * (N : ℝ) ^ (2 - a) := by
    simpa only [div_eq_mul_inv, mul_assoc] using hm
  exact hm'.trans hoff


end PaperP1.RandomizedPrivateClassObstructionUnderOrdinaryCensus
