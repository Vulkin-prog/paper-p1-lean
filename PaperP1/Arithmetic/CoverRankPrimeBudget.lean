module

public import PaperP1.Arithmetic.LogarithmicPrimeCount
public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Analysis.ElementaryLogGrowth

/-! # An explicit finite uniform small-prime cost for every three-block cover -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoverRankPrimeBudget

open PaperP1.LocalDefectBound PaperP1.CriticalBandScale

def constant (C₀ : ℝ) : ℝ := 3 * (14 * Real.log 2 * C₀ + 2)

theorem constant_pos {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : 0 < constant C₀ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold constant
  positivity

theorem finite_budget {B H : ℕ} (hB : 4 ≤ B) (hBH : B ≤ H) {C₀ : ℝ}
    (hH : (H : ℝ) ≤ C₀ * B) :
    (3 * (primeCount H + 2) : ℝ) ≤ constant C₀ * B / Real.log B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogB : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogmono : Real.log B ≤ Real.log H := Real.log_le_log hBpos (by exact_mod_cast hBH)
  have hpi : (primeCount H : ℝ) * Real.log H ≤ 14 * Real.log 2 * H :=
    LogarithmicPrimeCount.log_mul_primeCount_le (by omega)
  have hpi' := mul_le_mul_of_nonneg_left hlogmono (Nat.cast_nonneg (primeCount H))
  have hH' := mul_le_mul_of_nonneg_left hH (show 0 ≤ 14 * Real.log 2 by positivity)
  have hself := Real.log_le_self hBpos.le
  apply (le_div_iff₀ hlogB).mpr
  unfold constant
  nlinarith

theorem critical_width_at_least_four (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 4 ≤ L + 1 := by
  obtain ⟨Nwidth, hwidth⟩ := critical_band_scale C
  obtain ⟨Nlog, hlog⟩ := ElementaryLogGrowth.log_ge_eventually (4 / lowerScale)
  refine ⟨max 2 (max Nwidth Nlog), le_max_left _ _, ?_⟩
  intro N hN L hband
  have hlow := (hwidth N (by omega) L hband).1
  have hlogN := (hlog N (by omega)).1
  have hfour := (div_le_iff₀ lowerScale_pos).mp hlogN
  have hB : (4 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by nlinarith
  exact_mod_cast hB

end PaperP1.CoverRankPrimeBudget
