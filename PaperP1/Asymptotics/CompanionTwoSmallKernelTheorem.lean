module

public import PaperP1.Asymptotics.SharpTwoSmallKernelWindowCount

/-! # Companion T1.5 for every logarithmic window width, including its sharp lower bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompanionTwoSmallKernelTheorem

open Finset PaperP1.TwoSmallKernelWindows

theorem companion_T1_5 (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (β D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ((windows N L (L + 1) ((N : ℝ) ^ β)).card : ℝ) ≤ (N : ℝ) ^ (max β (7 / 12) + ε) := by
  obtain ⟨Nb, _hNb, hb⟩ := SharpTwoSmallKernelWindowCount.uniform_budget hHB hNG D D 1 (ε / 2)
    hD hD (by norm_num) (by positivity)
  obtain ⟨Nw, hw⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow D 1 1 (by norm_num)
  obtain ⟨Nk, hk⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow 2 0 (ε / 2) (by positivity)
  refine ⟨max 4 (max Nb (max Nw Nk)), by omega, ?_⟩
  intro N hN L hwidth
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hwidth' : ((L + 1 : ℕ) : ℝ) ≤ D * (Real.log N) ^ (1 : ℝ) := by simpa only [Real.rpow_one] using hwidth
  have hLN : L ≤ N := by
    have hh : ((L + 1 : ℕ) : ℝ) ≤ N := by simpa only [Real.rpow_one] using hwidth'.trans (hw N (by omega))
    have hnL : L + 1 ≤ N := by exact_mod_cast hh
    omega
  have hcount := hb N (by omega) (L + 1) L ((N : ℝ) ^ β) hwidth hwidth' hLN (by positivity)
  have hβ : (N : ℝ) ^ β ≤ (N : ℝ) ^ (max β (7 / 12)) := Real.rpow_le_rpow_of_exponent_le hn₁ (le_max_left _ _)
  have hbase : (N : ℝ) ^ (7 / 12 : ℝ) ≤ (N : ℝ) ^ (max β (7 / 12)) := Real.rpow_le_rpow_of_exponent_le hn₁ (le_max_right _ _)
  have htwo : (2 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by simpa only [Real.rpow_zero, mul_one] using hk N (by omega)
  have hsum : (N : ℝ) ^ β + (N : ℝ) ^ (7 / 12 : ℝ) ≤ (N : ℝ) ^ (max β (7 / 12)) * (N : ℝ) ^ (ε / 2) := by
    have hm := mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hn.le (max β (7 / 12)))
    linarith only [hβ, hbase, hm]
  calc
    _ ≤ ((N : ℝ) ^ β + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ (ε / 2) := hcount
    _ ≤ ((N : ℝ) ^ (max β (7 / 12)) * (N : ℝ) ^ (ε / 2)) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hn, add_halves, ← Real.rpow_add hn]

theorem companion_T1_5_sharp (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (β D ε : ℝ) (hβlo : 7 / 12 ≤ β) (hβhi : β < 1) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, 2 ≤ L →
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      (N : ℝ) ^ (β - ε) ≤ ((windows N L (L + 1) ((N : ℝ) ^ β)).card : ℝ) ∧
        ((windows N L (L + 1) ((N : ℝ) ^ β)).card : ℝ) ≤ (N : ℝ) ^ (β + ε) := by
  obtain ⟨Nu, _hNu, hu⟩ := companion_T1_5 hHB hNG β D ε hD hε
  obtain ⟨Nl, _hNl, hl⟩ := TwoSmallKernelWindows.uniform_lower β ε (by linarith only [hβlo]) hβhi hε
  refine ⟨max 4 (max Nu Nl), by omega, ?_⟩
  intro N hN L hL hwidth
  exact ⟨hl N (by omega) L (L + 1) hL, by simpa only [max_eq_left hβlo] using hu N (by omega) L hwidth⟩

end PaperP1.CompanionTwoSmallKernelTheorem
