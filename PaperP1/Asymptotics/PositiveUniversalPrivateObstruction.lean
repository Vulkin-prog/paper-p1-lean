module

public import PaperP1.Asymptotics.PositiveRandomizedPrivateObstruction
public import PaperP1.Model.PrivateForcingMeasureObservation

/-! # Internal positive-constant obstruction for every measurable private forcing

Only the literal physical prescription and unchanged nonpivot prime signs
are required on full-good sources. The original forcing is arbitrary at
every other retained source, and its auxiliary probability space is arbitrary.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveUniversalPrivateObstruction

open MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.RandomizedHybridField
  PaperP1.LogFifthPivotCutoff

theorem randomized_lower (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1 / 10) :
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E Y M : ℕ, ∀ i : Fin 2,
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
      ∀ F : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) Y →
        SampleSpace M → Ξ → SampleSpace M,
      (∀ j u s, MeasurableSet {ξ : Ξ | g j u ξ = s}) →
      (∀ j ω r s, MeasurableSet {ξ : Ξ | F j ω ξ r = s}) →
      (∀ j, j.val ∈ PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N) → ∀ ω ξ,
        PaperP1.PrivateValueSystem.valueSystem M (fun k : Fin (L + i.val + 1) ↦ j.val + k.val) (F j ω ξ) =
          PaperP1.RandomizedPrivatePalmForcing.orientedWord b
            (g j (PaperP1.PrivateValueSystem.valueSystem M (fun k : Fin (L + i.val + 1) ↦ j.val + k.val) ω) ξ)) →
      (∀ j, ∀ hj : j.val ∈ PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N),
        ∀ ω ξ, ∀ r : PrimeUpTo M, (∀ k, r ≠ fullPivots A j hj k) → F j ω ξ r = ω r) →
      r * (PaperP1.AnchoredPrivateField.rate (L + i.val)) ^ 2 / 2 * (N : ℝ) ^ (2 - a) ≤
        PaperP1.PrivateForcingMeasureObservation.offsite μ b F := by
  obtain ⟨r, hr, N₀, h⟩ := PaperP1.PositiveRandomizedPrivateObstruction.finite_lower C D a hD ha ha1
  refine ⟨r, hr, N₀, ?_⟩
  intro N hN L E Y M i hL hBY hYZ hwidth hcut hband anchor A Ξ _ μ _ b g F hg hF hhit hout
  have hm := PaperP1.PrivateForcingMeasureObservation.encode_measurable g F hg hF
  have haF := PaperP1.PrivateForcingMeasureObservation.agrees_of_prescription A b g F hhit hout
  have hoff := h N hN L E Y M i hL hBY hYZ hwidth hcut hband anchor A
    (PaperP1.PrivateForcingMeasureObservation.Observation M (L + i.val)
      (PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) Y))
    (PaperP1.PrivateForcingMeasureObservation.law μ g F hm) b
    PaperP1.PrivateForcingMeasureObservation.observedOrientation
    (PaperP1.PrivateForcingMeasureObservation.observedForce A b)
    (PaperP1.PrivateForcingMeasureObservation.observed_agrees A b)
  rw [PaperP1.PrivateForcingMeasureObservation.offsite_observation A μ b g F hm haF] at hoff
  exact hoff

end PaperP1.PositiveUniversalPrivateObstruction
