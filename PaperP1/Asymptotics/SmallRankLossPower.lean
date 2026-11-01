module

public import PaperP1.Model.LocalRigidityConsequences
public import PaperP1.Asymptotics.CriticalBandScale

/-! # Explicit subpower cost of a small effective rank loss in the critical band -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallRankLossPower

open PaperP1.CriticalBandScale

theorem loss_power {N L : ℕ} (hN : 2 ≤ N) (η : ℝ) (hη : 0 ≤ η)
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N) :
    (2 : ℝ) ^ (η * L) ≤ (N : ℝ) ^ (η * upperScale * Real.log 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : (L : ℝ) ≤ upperScale * Real.log N :=
    (show (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ L).trans hwidth
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hNr]
  apply Real.exp_le_exp.mpr
  convert mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL hη)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) using 1; ring

theorem low_sum_bound {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N) (η : ℝ) (hη : 0 ≤ η) :
    (N : ℝ) * (2 * (2 ^ L : ℝ)⁻¹) * (2 : ℝ) ^ (η * L) ≤
      (2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (η * upperScale * Real.log 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnominal := LocalRigidityConsequences.nominal_marginal_bound hN hband
  have hscale : (N : ℝ) * (2 * (2 ^ L : ℝ)⁻¹) ≤ 2 * (2 : ℝ) ^ C := by
    calc
      _ ≤ (N : ℝ) * (2 * ((2 : ℝ) ^ C / N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnominal (by norm_num)) hNr.le
      _ = _ := by field_simp
  exact mul_le_mul hscale (loss_power hN η hη hwidth) (by positivity) (by positivity)

end PaperP1.SmallRankLossPower
