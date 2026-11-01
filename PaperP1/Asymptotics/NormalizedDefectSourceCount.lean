module

public import PaperP1.Arithmetic.NormalizedDefectSources
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # Actual nonprivate normalized source pairs have a uniform square-root host count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedDefectSourceCount

open PaperP1.NormalizedDefectSources PaperP1.GlobalDefectCount PaperP1.CriticalBandScale

theorem bad_sources_rate (C : ℝ) (D a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
        ((badSources N H a b L).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Ndef, hdef⟩ := global_defect_count_le_rpow_eventually
    (3 * (b : ℝ)) ((D : ℝ) * upperScale) (by positivity)
    (mul_nonneg (Nat.cast_nonneg D) upperScale_pos.le) (ε / 2) (by linarith)
  obtain ⟨Npoly, hpoly⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 2 3 (ε / 2) (by linarith)
  refine ⟨max Ngeom (max Ndef Npoly), ?_⟩
  intro N hN L H hcrit hcut hH
  obtain ⟨hNtwo, _, _, hthin, _, hB⟩ := hgeom N (by omega) L hcrit
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hHreal : (H : ℝ) ≤ ((D : ℝ) * upperScale) * Real.log N := by
    have hc : (H : ℝ) ≤ (D : ℝ) * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hH
    exact hc.trans (by nlinarith only [hB, mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg D)])
  have hX : ((b * (2 * N + L) : ℕ) : ℝ) ≤ (3 * (b : ℝ)) * N := by
    have hLN : L ≤ N := by omega
    have hc : b * (2 * N + L) ≤ 3 * b * N := by nlinarith
    exact_mod_cast hc
  have hdefCount := hdef N (by omega) H (b * (2 * N + L)) hHreal hX
  have hfactor : 2 * ((L + 1 : ℕ) : ℝ) ^ 3 ≤ (N : ℝ) ^ (ε / 2) := by
    have hp := hpoly N (by omega) L hB
    simpa only [Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (L + 1 : ℝ) ^ 3)] using hp
  calc
    _ ≤ 2 * ((L + 1 : ℕ) : ℝ) ^ 3 * (positiveDefectsBelow H (b * (2 * N + L))).card := by
      exact_mod_cast bad_sources_card hNtwo ha hb hab hcut
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 / 2 + ε / 2) :=
      mul_le_mul hfactor hdefCount (Nat.cast_nonneg _) (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

end PaperP1.NormalizedDefectSourceCount
