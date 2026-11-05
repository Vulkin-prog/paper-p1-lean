module

public import PaperP1.Asymptotics.RandomizedPrivateClassCostFromCensus
public import PaperP1.Asymptotics.PositiveAnchorCostScale

/-! # Internal positive-constant cost obstruction for every finite randomized private forcing

The literal clean source census supplies a fixed positive constant. The
randomized half-factor and exact private-forcing class are retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveRandomizedPrivateObstruction

open PaperP1.Arithmetic PaperP1.Model PaperP1.RandomizedHybridField
  PaperP1.LogFifthPivotCutoff PaperP1.AnchoredCostErrorScale

theorem finite_lower (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1 / 10) :
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E Y M : ℕ, ∀ i : Fin 2,
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
      r * (PaperP1.AnchoredPrivateField.rate (L + i.val)) ^ 2 / 2 * (N : ℝ) ^ (2 - a) ≤ PaperP1.PositiveForcingCostLower.offsite Finset.univ (law (M := M) P) (indicator b) F := by
  obtain ⟨r, hr, NR, hR⟩ := PaperP1.PositiveAnchorCostScale.uniform_bracket_lower C D a hD ha ha1
  obtain ⟨NC, hc⟩ := PaperP1.RandomizedPrivateClassCostFromCensus.uniform_ordinary_candidates_lower
    D hD (errorExponent a) (errorExponent_pos ha1)
  obtain ⟨NZ, hz⟩ := uniform_data D (1 / 4) (by norm_num) (by norm_num)
  refine ⟨r, hr, max NR (max NC NZ), ?_⟩
  intro N hN L E Y M i hL hBY hYZ hwidth hM hcrit anchor A Ξ _ P b g F hF
  have hKB : L + i.val + 1 ≤ L + E + 2 := by have := i.isLt; omega
  obtain ⟨_hbig, _hZ, _hratio, hcollision, hupper⟩ := hz N (by omega) (L + E + 2) (L + i.val) hwidth hKB
  have hfinite := hc N (by omega) (L + E + 2) Y (cutoff N) (L + i.val) M ((N : ℝ) ^ a)
    (by omega) hKB hBY hwidth hYZ hupper hM hcollision anchor A Ξ P b g F hF
  have hbracket := hR N (by omega) L i (L + E + 2) hL hKB hwidth hcrit
  have hh := (mul_le_mul_of_nonneg_left hbracket (by positivity :
    (0 : ℝ) ≤ (PaperP1.AnchoredPrivateField.rate (L + i.val)) ^ 2 / 2)).trans hfinite
  convert hh using 1
  ring

end PaperP1.PositiveRandomizedPrivateObstruction
