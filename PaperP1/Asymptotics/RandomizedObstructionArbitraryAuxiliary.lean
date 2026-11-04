module

public import PaperP1.Asymptotics.RandomizedHybridObstructionUnderOrdinaryCensus
public import PaperP1.Model.RandomizedHybridMeasureAuxiliary

/-! # The actual randomized half-factor obstruction for arbitrary auxiliary laws

The remaining source census is purely arithmetic. Auxiliary measures,
measurable source-word orientations, original anchor rules and actual
hybrid costs are all quantified after the uniform threshold.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedObstructionArbitraryAuxiliary

open MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.RandomizedHybridField
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
      ∀ (Ξ : Type*) [MeasurableSpace Ξ], ∀ μ : Measure Ξ, ∀ [IsProbabilityMeasure μ],
      ∀ b : Fin (L + i.val + 1) → F₂,
      ∀ g : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) Y →
        (Fin (L + i.val + 1) → F₂) → Ξ → F₂,
      (∀ j u s, MeasurableSet {ξ : Ξ | g j u ξ = s}) →
      (1 - η) * (PaperP1.AnchoredPrivateField.rate (L + i.val)) ^ 2 / 2 * (N : ℝ) ^ (2 - a) ≤
        PaperP1.RandomizedHybridMeasureAuxiliary.offsite A μ b g := by
  obtain ⟨N₀, h⟩ := PaperP1.RandomizedHybridObstructionUnderOrdinaryCensus.randomized_under_census
    C D a hD ha ha1 hCensus η hη
  refine ⟨N₀, ?_⟩
  intro N hN L E Y M i hL hBY hYZ hwidth hcut hband anchor A Ξ _ μ _ b g hg
  have hm := PaperP1.FiniteOrientationObservation.encode_measurable g hg
  have hoff := h N hN L E Y M i hL hBY hYZ hwidth hcut hband anchor A
    (PaperP1.FiniteOrientationObservation.Table
      (PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) Y) (Fin (L + i.val + 1) → F₂))
    (PaperP1.FiniteOrientationObservation.law μ g hm) b PaperP1.RandomizedHybridMeasureAuxiliary.observedOrientation
  rw [PaperP1.RandomizedHybridMeasureAuxiliary.offsite_observation A μ b g hm] at hoff
  exact hoff

end PaperP1.RandomizedObstructionArbitraryAuxiliary
