module

public import PaperP1.Arithmetic.QuadraticDegreeUniformFieldCount
public import PaperP1.Analysis.BinaryLogarithmicBudget

/-! # The actual real-height natural-logarithmic quadratic plane bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticPlaneUniformBound

open Polynomial DegreeUniformAffineParameters

theorem binary_budget_le_real_log (N : ℕ) (hN : 1 ≤ N) (H : ℝ) (hH : 2 < H)
    (hNH : (N : ℝ) ≤ H) :
    (logarithmicBudget N : ℝ) ≤ (2 / Real.log 2) * Real.log H := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := (abs_le.mp (BinaryLogarithmicBudget.critical_band N hN)).2
  have hlogNH := Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hNH
  have hquot := div_le_div_of_nonneg_right hlogNH hlog2.le
  have hlogH := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hH.le
  have hone : 1 ≤ Real.log H / Real.log 2 := (le_div_iff₀ hlog2).mpr (by simpa only [one_mul] using hlogH)
  calc
    _ ≤ 2 * (Real.log H / Real.log 2) := by linarith only [hb, hquot, hone]
    _ = _ := by ring

theorem uniform_bound : ∃ c : ℝ, 0 < c ∧ PlaneCurvePointCount.UniformBound c 17 := by
  obtain ⟨C, hC, hcount⟩ := QuadraticDegreeUniformFieldCount.field_count
  let A : ℝ := 2 / Real.log 2
  have hA : 0 < A := div_pos (by norm_num) (Real.log_pos (by norm_num))
  refine ⟨(3 + C) * A ^ 17, by positivity, ?_⟩
  intro K _hK _hchar _halg P hP hD H hH
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg (by linarith : (1 : ℝ) ≤ H)
  let N : ℕ := ⌊H⌋₊
  have hN : 1 ≤ N := by
    apply Nat.le_floor
    norm_num only [Nat.cast_one]
    linarith only [hH]
  have hNH : (N : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hLH : (logarithmicBudget N : ℝ) ≤ A * Real.log H := binary_budget_le_real_log N hN H hH hNH
  have hpow : (logarithmicBudget N : ℝ) ^ 17 ≤ (A * Real.log H) ^ 17 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hLH 17
  have hL : (1 : ℝ) ≤ logarithmicBudget N := by
    exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hweight : 1 ≤ A ^ 17 * Real.log H ^ 17 := by
    simpa only [mul_pow] using (one_le_pow₀ hL : (1 : ℝ) ≤ (logarithmicBudget N : ℝ) ^ 17).trans hpow
  change ((PlaneCurvePointCount.grid P N).card : ℝ) ≤
    ((3 + C) * A ^ 17) * CurveDegreeProfile.profile H (PlaneCurvePointCount.degree P : ℝ) *
      Real.log H ^ ((17 : ℕ) : ℝ)
  rw [Real.rpow_natCast]
  by_cases hlin : PlaneCurvePointCount.degree P = 1
  · have hline := LinearPlaneGridBound.linear_real_grid_card P hP hlin H hH
    have hcoef : 3 ≤ (3 + C) * (A ^ 17 * Real.log H ^ 17) :=
      (show (3 : ℝ) ≤ 3 + C by linarith only [hC]).trans
        (le_mul_of_one_le_right (by positivity) hweight)
    have hm := mul_le_mul_of_nonneg_right hcoef (by linarith : (0 : ℝ) ≤ H)
    simp only [CurveDegreeProfile.profile, hlin, Nat.cast_one, one_pow, one_div_one, Real.rpow_one, one_mul]
    exact hline.trans (by convert hm using 1; ring)
  · have hD2 : 2 ≤ PlaneCurvePointCount.degree P := by omega
    have hb := hcount (PlaneCurvePointCount.degree P) N hD2 hN K P rfl hP
    have hroot : (N : ℝ) ^ (1 / (PlaneCurvePointCount.degree P : ℝ)) ≤
        H ^ (1 / (PlaneCurvePointCount.degree P : ℝ)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hNH (by positivity)
    have hprofile : 0 ≤ CurveDegreeProfile.profile H (PlaneCurvePointCount.degree P : ℝ) := by
      unfold CurveDegreeProfile.profile
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ H) _)
    calc
      _ ≤ C * QuadraticDegreeUniformFieldCount.profile (PlaneCurvePointCount.degree P) N := hb
      _ = C * (PlaneCurvePointCount.degree P : ℝ) ^ 2 * (logarithmicBudget N : ℝ) ^ 17 *
          (N : ℝ) ^ (1 / (PlaneCurvePointCount.degree P : ℝ)) := by
        unfold QuadraticDegreeUniformFieldCount.profile
        ring
      _ ≤ C * (PlaneCurvePointCount.degree P : ℝ) ^ 2 * (A * Real.log H) ^ 17 *
          H ^ (1 / (PlaneCurvePointCount.degree P : ℝ)) := by gcongr
      _ = C * A ^ 17 * CurveDegreeProfile.profile H (PlaneCurvePointCount.degree P : ℝ) * Real.log H ^ 17 := by
        rw [mul_pow]
        unfold CurveDegreeProfile.profile
        ring
      _ ≤ _ := by gcongr; linarith only [hC]

end PaperP1.QuadraticPlaneUniformBound
