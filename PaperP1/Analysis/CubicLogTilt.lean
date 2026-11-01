module

public import PaperP1.Analysis.ElementaryLogGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The variable Rankin tilt at a cubic logarithmic prime budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CubicLogTilt

def budget (A H : ℝ) : ℝ := A * H ^ 3 / Real.log H

def tilt (A H : ℝ) : ℝ := 1 - Real.log H / Real.log (budget A H)

theorem budget_pos {A H : ℝ} (hA : 1 ≤ A) (hH : 0 < H) (hh : 0 < Real.log H) : 0 < budget A H := by
  exact div_pos (mul_pos (by linarith) (pow_pos hH _)) hh

theorem log_budget {A H : ℝ} (hA : 1 ≤ A) (hH : 0 < H) (hh : 0 < Real.log H) :
    Real.log (budget A H) = Real.log A + 3 * Real.log H - Real.log (Real.log H) := by
  rw [budget, Real.log_div (by positivity : A * H ^ 3 ≠ 0) hh.ne',
    Real.log_mul (by linarith : A ≠ 0) (pow_ne_zero _ hH.ne'), Real.log_pow]
  norm_num

theorem log_budget_bounds {A H : ℝ} (hA : 1 ≤ A) (hH : 0 < H)
    (hh : 4096 ≤ Real.log H) (hlogA : Real.log A ≤ Real.log H) :
    5 / 2 * Real.log H ≤ Real.log (budget A H) ∧ Real.log (budget A H) ≤ 4 * Real.log H := by
  have hlogh := ElementaryLogGrowth.thirtyTwo_mul_log_le hh
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlogh0 : 0 ≤ Real.log (Real.log H) := Real.log_nonneg (by linarith)
  rw [log_budget hA hH (by linarith)]
  constructor <;> linarith

theorem budget_gt_one {A H : ℝ} (hA : 1 ≤ A) (hH : 0 < H)
    (hh : 4096 ≤ Real.log H) (hlogA : Real.log A ≤ Real.log H) : 1 < budget A H := by
  have hbound := (log_budget_bounds hA hH hh hlogA).1
  exact (Real.log_pos_iff (budget_pos hA hH (by linarith)).le).mp (by linarith)

theorem tilt_bounds {A H : ℝ} (hA : 1 ≤ A) (hH : 0 < H)
    (hh : 4096 ≤ Real.log H) (hlogA : Real.log A ≤ Real.log H) :
    3 / 5 ≤ tilt A H ∧ tilt A H ≤ 3 / 4 := by
  obtain ⟨hlo, hhi⟩ := log_budget_bounds hA hH hh hlogA
  have hlogY : 0 < Real.log (budget A H) := by linarith
  have hloDiv : (1 / 4 : ℝ) ≤ Real.log H / Real.log (budget A H) := (le_div_iff₀ hlogY).mpr (by linarith)
  have hhiDiv : Real.log H / Real.log (budget A H) ≤ 2 / 5 := (div_le_iff₀ hlogY).mpr (by linarith)
  unfold tilt
  constructor <;> linarith

theorem budget_tilt_power {A H : ℝ} (hA : 1 ≤ A) (hH : 0 < H)
    (hh : 4096 ≤ Real.log H) (hlogA : Real.log A ≤ Real.log H) :
    (budget A H) ^ (1 - tilt A H) = H := by
  have hYpos := budget_pos hA hH (by linarith : 0 < Real.log H)
  have hlogY : Real.log (budget A H) ≠ 0 := (Real.log_pos (budget_gt_one hA hH hh hlogA)).ne'
  rw [Real.rpow_def_of_pos hYpos, tilt]
  have heq : Real.log (budget A H) * (1 - (1 - Real.log H / Real.log (budget A H))) = Real.log H := by
    field_simp
    ring
  rw [heq, Real.exp_log hH]

theorem ratio_lower {A H : ℝ} (hA : 1 ≤ A) (hH : 0 < H)
    (hh : 4096 ≤ Real.log H) (hlogA : Real.log A ≤ Real.log H) :
    1 / 3 + (Real.log (Real.log H) - Real.log A) / (9 * Real.log H) ≤
      Real.log H / Real.log (budget A H) := by
  have hhpos : 0 < Real.log H := by linarith
  have hlogY := Real.log_pos (budget_gt_one hA hH hh hlogA)
  apply (le_div_iff₀ hlogY).mpr
  have heq : (1 / 3 + (Real.log (Real.log H) - Real.log A) / (9 * Real.log H)) * Real.log (budget A H) =
      Real.log H - (Real.log (Real.log H) - Real.log A) ^ 2 / (9 * Real.log H) := by
    rw [log_budget hA hH hhpos]
    field_simp
    ring
  rw [heq]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))

theorem tilted_main_bound {A H : ℝ} (hA : 1 ≤ A) (hH : 0 < H)
    (hh : 4096 ≤ Real.log H) (hlogA : Real.log A ≤ Real.log H) :
    tilt A H * H ≤ 2 / 3 * H - H * Real.log (Real.log H) / (9 * Real.log H) +
      (Real.log A / 9) * (H / Real.log H) := by
  have h := mul_le_mul_of_nonneg_right (ratio_lower hA hH hh hlogA) hH.le
  unfold tilt
  rw [add_mul] at h
  convert (show (1 - Real.log H / Real.log (budget A H)) * H ≤
    2 / 3 * H - ((Real.log (Real.log H) - Real.log A) / (9 * Real.log H)) * H by linarith) using 1
  ring

theorem log_scale_bounds {H : ℝ} (hH : 0 < H) (hh : 1 ≤ Real.log H) :
    1 ≤ H / Real.log H ∧ Real.log H ≤ 4 * (H / Real.log H) := by
  have hhpos : 0 < Real.log H := by linarith
  have hlogSelf := Real.log_le_self hH.le
  have hsq := ElementaryLogGrowth.square_le_four_mul_exp hhpos.le
  rw [Real.exp_log hH] at hsq
  constructor
  · exact (le_div_iff₀ hhpos).mpr (by linarith)
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hhpos).mpr
    nlinarith

end PaperP1.CubicLogTilt
