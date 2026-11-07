module

public import PaperP1.Asymptotics.PrintedDeterministicAnchorObstruction
public import PaperP1.Asymptotics.PrintedRandomizedPrivateObstruction
public import PaperP1.Analysis.UnconditionalOrdinarySourceCensus


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UnconditionalPrintedAnchorObstruction

section deterministic
open PaperP1.Arithmetic PaperP1.Model PaperP1.AnchoredPrivateField
  PaperP1.PrintedAnchorObstructionParameters PaperP1.LogarithmicOrdinaryCensusBridge

theorem companion_T19_17 (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1 / 10)
    (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E M : ℕ, ∀ i : Fin 2,
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N → 2 * N + (L + E + 2) ≤ M →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2)
        (2 * (L + E + 2)) → Fin (L + i.val + 1),
      ∀ A : Data M (2 * (L + E + 2)) (L + i.val)
        (PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2))) anchor,
      ∀ b : Fin (L + i.val + 1) → F₂,
      (1 - η) * nominal N L i.val a ≤ offsite A b := by
  have hCensus := UnconditionalOrdinarySourceCensus.ordinary_census C a ha
  obtain ⟨NO, hO⟩ := PaperP1.AnchoredObstructionUnderOrdinaryCensus.deterministic_under_census
    C D a hD ha ha1 hCensus η hη
  obtain ⟨NP, hP⟩ := uniform_parameters C D
  refine ⟨max NO NP, ?_⟩
  intro N hN L E M i hwidth hM hband anchor A b
  obtain ⟨hL, hcut⟩ := hP N (by omega) L E hband hwidth
  have hoff := hO N (by omega) L E (2 * (L + E + 2)) M i hL (by omega) hcut hwidth hM hband anchor A b
  rw [nominal_eq (by omega : 0 < N)]
  simpa only [mul_assoc] using hoff

end deterministic

section randomized
open MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.RandomizedHybridField
  PaperP1.PrintedAnchorObstructionParameters PaperP1.LogarithmicOrdinaryCensusBridge
  PaperP1.LogFifthPivotCutoff

theorem companion_T19_17_randomized (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1 / 10)
    (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E M : ℕ, ∀ i : Fin 2,
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N → 2 * N + (L + E + 2) ≤ M →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)) → Fin (L + i.val + 1),
      ∀ A : Data M (2 * (L + E + 2)) (L + i.val) (PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)))
        (PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N)) anchor,
      ∀ (Ξ : Type*) [MeasurableSpace Ξ], ∀ μ : Measure Ξ, ∀ [IsProbabilityMeasure μ],
      ∀ b : Fin (L + i.val + 1) → F₂,
      ∀ g : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)) →
        (Fin (L + i.val + 1) → F₂) → Ξ → F₂,
      ∀ F : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)) →
        SampleSpace M → Ξ → SampleSpace M,
      (∀ j u s, MeasurableSet {ξ : Ξ | g j u ξ = s}) →
      (∀ j ω r s, MeasurableSet {ξ : Ξ | F j ω ξ r = s}) →
      (∀ j, j.val ∈ PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N) → ∀ ω ξ,
        PaperP1.PrivateValueSystem.valueSystem M (fun k : Fin (L + i.val + 1) ↦ j.val + k.val) (F j ω ξ) =
          PaperP1.RandomizedPrivatePalmForcing.orientedWord b
            (g j (PaperP1.PrivateValueSystem.valueSystem M (fun k : Fin (L + i.val + 1) ↦ j.val + k.val) ω) ξ)) →
      (∀ j, ∀ hj : j.val ∈ PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N),
        ∀ ω ξ, ∀ r : PrimeUpTo M, (∀ k, r ≠ fullPivots A j hj k) → F j ω ξ r = ω r) →
      (1 - η) / 2 * nominal N L i.val a ≤
        PaperP1.PrivateForcingMeasureObservation.offsite μ b F := by
  have hCensus := UnconditionalOrdinarySourceCensus.ordinary_census C a ha
  obtain ⟨NO, hO⟩ := PaperP1.UniversalPrivateObstructionArbitraryAuxiliary.randomized_under_census
    C D a hD ha ha1 hCensus η hη
  obtain ⟨NP, hP⟩ := uniform_parameters C D
  refine ⟨max NO NP, ?_⟩
  intro N hN L E M i hwidth hM hband anchor A Ξ _ μ _ b g F hg hF hhit hout
  obtain ⟨hL, hcut⟩ := hP N (by omega) L E hband hwidth
  have hoff := hO N (by omega) L E (2 * (L + E + 2)) M i hL (by omega) hcut
    hwidth hM hband anchor A Ξ μ b g F hg hF hhit hout
  calc
    _ = (1 - η) * (PaperP1.AnchoredPrivateField.rate (L + i.val)) ^ 2 / 2 * (N : ℝ) ^ (2 - a) := by
      rw [nominal_eq (by omega : 0 < N)]
      ring
    _ ≤ _ := hoff

end randomized

end PaperP1.UnconditionalPrintedAnchorObstruction
