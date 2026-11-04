module

public import PaperP1.Asymptotics.PrintedAnchorObstructionParameters
public import PaperP1.Asymptotics.LogarithmicOrdinaryCensusBridge

/-! # T19.17: the actual deterministic anchor obstruction at the printed parameters

The only unformalized mathematical input is the specified fixed-parameter
ordinary smooth-number short-interval statement. All anchor choices and
moving maximal support widths follow the single uniform threshold.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrintedDeterministicAnchorObstruction

open PaperP1.Arithmetic PaperP1.Model PaperP1.AnchoredPrivateField
  PaperP1.PrintedAnchorObstructionParameters PaperP1.LogarithmicOrdinaryCensusBridge

theorem deterministic_under_short_interval_input (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1 / 10) (hInput : CorollarySixLogInput a)
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
  have hCensus := ordinary_census_of_corollary_six C a ha hInput
  obtain ⟨NO, hO⟩ := PaperP1.AnchoredObstructionUnderOrdinaryCensus.deterministic_under_census
    C D a hD ha ha1 hCensus η hη
  obtain ⟨NP, hP⟩ := uniform_parameters C D
  refine ⟨max NO NP, ?_⟩
  intro N hN L E M i hwidth hM hband anchor A b
  obtain ⟨hL, hcut⟩ := hP N (by omega) L E hband hwidth
  have hoff := hO N (by omega) L E (2 * (L + E + 2)) M i hL (by omega) hcut hwidth hM hband anchor A b
  rw [nominal_eq (by omega : 0 < N)]
  simpa only [mul_assoc] using hoff

end PaperP1.PrintedDeterministicAnchorObstruction
