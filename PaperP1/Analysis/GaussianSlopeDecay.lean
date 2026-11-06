module

public import PaperP1.Analysis.LogarithmicExponentialSum

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GaussianSlopeDecay
open PaperP1

theorem quadratic_bound (x c : ℝ) :
    Real.exp (-x^2) ≤ Real.exp (c^2/4)*Real.exp (-c*x) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [sq_nonneg (x-c/2)]

theorem gaussian_le_one (x : ℝ) : Real.exp (-x^2) ≤ 1 := by
  have hh := Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg x))
  simpa only [Real.exp_zero] using hh

theorem absolute_decay_bound (x : ℝ) :
    Real.exp (-x^2) ≤ Real.exp 1*Real.exp (-2*|x|) := by
  have hh := quadratic_bound |x| 2
  norm_num only [sq_abs,show (2 : ℝ)^2/4=1 by norm_num] at hh
  exact hh

theorem slope_decay_bound (x : ℝ) :
    (1+2*|x|)*Real.exp (-x^2) ≤ 2*Real.exp 2*Real.exp (-2*|x|) := by
  have hExp := Real.add_one_le_exp (x^2/2)
  have hSquare := sq_nonneg (|x|-1)
  have hAbs := sq_abs x
  have hFront : 1+2*|x| ≤ 2*Real.exp (x^2/2) := by nlinarith only [hExp,hSquare,hAbs]
  have hLast : Real.exp (-x^2/2) ≤ Real.exp 2*Real.exp (-2*|x|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := sq_nonneg (|x|-2)
    nlinarith only [hh,hAbs]
  calc
    _ ≤ (2*Real.exp (x^2/2))*Real.exp (-x^2) :=
      mul_le_mul_of_nonneg_right hFront (Real.exp_pos _).le
    _ = 2*Real.exp (-x^2/2) := by
      rw [mul_assoc,← Real.exp_add]
      rw [show x^2/2+-x^2=-x^2/2 by ring]
    _ ≤ 2*(Real.exp 2*Real.exp (-2*|x|)) := mul_le_mul_of_nonneg_left hLast (by norm_num)
    _ = _ := by ring

theorem slope_uniform_bound (x : ℝ) :
    (1+2*|x|)*Real.exp (-x^2) ≤ 2*Real.exp 2 := by
  have hDecay : Real.exp (-2*|x|) ≤ 1 := by
    have hh := Real.exp_le_exp.mpr (show -2*|x| ≤ (0 : ℝ) by nlinarith only [abs_nonneg x])
    simpa only [Real.exp_zero] using hh
  exact (slope_decay_bound x).trans (by
    have hh := mul_le_mul_of_nonneg_left hDecay (by positivity : 0 ≤ 2*Real.exp 2)
    simpa only [mul_one] using hh)
end PaperP1.GaussianSlopeDecay
