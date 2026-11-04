module

public import PaperP1.Arithmetic.BoundedNormalizedDefectPairs
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # Uniform square-root defect-pair hosts on the whole bounded source interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedNormalizedDefectPairCount

open PaperP1.BoundedNormalizedDefectPairs PaperP1.GlobalDefectCount PaperP1.CriticalBandScale

theorem uniform_bound (C D : ℝ) (hD : 0 ≤ D) (Q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L H a b : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → a ≤ b → b ≤ Q →
      (H : ℝ) ≤ D * ((L + 1 : ℕ) : ℝ) →
      ((pairs M H a b L).card : ℝ) ≤ (M : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨MG, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨MD, hD₀⟩ := global_defect_count_le_rpow_eventually
    (2 * (Q : ℝ)) (D * upperScale) (by positivity) (mul_nonneg hD upperScale_pos.le)
    (ε / 2) (by positivity)
  obtain ⟨MP, hP⟩ := PaperP1.LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le ((8 * Q + 2 : ℕ) : ℝ) 2 (ε / 2) (by positivity)
  refine ⟨max MG (max MD MP), ?_⟩
  intro M hM L H a b hcrit ha hab hbQ hH
  obtain ⟨_hMtwo, _hBlarge, _hBtwo, hthin, _hBlo, hBhi⟩ := hG M (by omega) L hcrit
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hHlog : (H : ℝ) ≤ (D * upperScale) * Real.log M := by
    exact hH.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hBhi hD)
  have hX : ((b * (M + L) : ℕ) : ℝ) ≤ (2 * (Q : ℝ)) * M := by
    have hnat : b * (M + L) ≤ 2 * Q * M := by
      calc
        _ ≤ Q * (M + M) := Nat.mul_le_mul hbQ (by omega)
        _ = _ := by ring
    exact_mod_cast hnat
  have hdef := hD₀ M (by omega) H (b * (M + L)) hHlog hX
  have hfactor : ((8 * Q + 2 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (M : ℝ) ^ (ε / 2) := by
    have hp := hP M (by omega) L hBhi
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((8 * Q + 2 : ℕ) : ℝ) * (L + 1 : ℝ) ^ 2)] at hp
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  have hpre : ((2 * (L + 1) * (2 * ((a + b) * (L + 1)) + 1) : ℕ) : ℝ) ≤
      ((8 * Q + 2 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast prefactor_bound hab hbQ
  calc
    _ ≤ ((2 * (L + 1) * (2 * ((a + b) * (L + 1)) + 1) : ℕ) : ℝ) *
        (positiveDefectsBelow H (b * (M + L))).card := by
      exact_mod_cast pairs_card ha (ha.trans_le hab) hab
    _ ≤ (((8 * Q + 2 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 2) *
        (positiveDefectsBelow H (b * (M + L))).card := mul_le_mul_of_nonneg_right hpre (Nat.cast_nonneg _)
    _ ≤ (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (1 / 2 + ε / 2) :=
      mul_le_mul hfactor hdef (Nat.cast_nonneg _) (Real.rpow_nonneg hm.le _)
    _ = (M : ℝ) ^ (1 / 2 + ε) := by rw [← Real.rpow_add hm]; congr 1; ring

end PaperP1.BoundedNormalizedDefectPairCount
