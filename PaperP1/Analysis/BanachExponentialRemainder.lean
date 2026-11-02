module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Tactic.Positivity

/-! # Explicit exponential tails in a real Banach algebra

The estimates use the absolutely convergent exponential series. They require
no convolution logarithm and impose no small-norm restriction.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BanachExponentialRemainder

open Finset

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

omit [CompleteSpace A] in
theorem norm_term_le (x : A) (n : ℕ) :
    ‖((n.factorial : ℝ)⁻¹) • x ^ n‖ ≤ ‖x‖ ^ n / (n.factorial : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n.factorial : ℝ)⁻¹)]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity : 0 ≤ (n.factorial : ℝ)⁻¹)

omit [CompleteSpace A] in
theorem norm_tail_term_le (x : A) (n j : ℕ) :
    ‖(((j + n).factorial : ℝ)⁻¹) • x ^ (j + n)‖ ≤
      ‖x‖ ^ n * (‖x‖ ^ j / (j.factorial : ℝ)) := by
  have hf : (j.factorial : ℝ) ≤ (j + n).factorial := by
    exact_mod_cast Nat.factorial_le (show j ≤ j + n by omega)
  have hinv : ((j + n).factorial : ℝ)⁻¹ ≤ (j.factorial : ℝ)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr hf
  calc
    _ ≤ ‖x‖ ^ (j + n) / ((j + n).factorial : ℝ) := norm_term_le x (j + n)
    _ ≤ ‖x‖ ^ (j + n) / (j.factorial : ℝ) := by
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ ‖x‖ ^ (j + n))
    _ = _ := by rw [pow_add]; ring

theorem norm_exp_sub_partial_le (x : A) (n : ℕ) :
    ‖NormedSpace.exp x - ∑ j ∈ range n, ((j.factorial : ℝ)⁻¹) • x ^ j‖ ≤
      ‖x‖ ^ n * Real.exp ‖x‖ := by
  have ht := (hasSum_nat_add_iff' n).mpr
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have hr := (NormedSpace.expSeries_div_hasSum_exp ‖x‖).mul_left (‖x‖ ^ n)
  rw [← Real.exp_eq_exp_ℝ] at hr
  exact ht.norm_le_of_bounded hr (norm_tail_term_le x n)

theorem norm_exp_le (x : A) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  simpa only [range_zero, sum_empty, sub_zero, pow_zero, one_mul] using norm_exp_sub_partial_le x 0

theorem norm_exp_sub_one_le (x : A) :
    ‖NormedSpace.exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  simpa only [sum_range_succ, sum_range_zero, Nat.factorial_zero, Nat.cast_one,
    inv_one, pow_zero, one_smul, zero_add, pow_one] using norm_exp_sub_partial_le x 1

theorem norm_exp_sub_linear_le (x : A) :
    ‖NormedSpace.exp x - (1 + x)‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  simpa only [sum_range_succ, sum_range_zero, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, inv_one, pow_zero, one_smul, zero_add, pow_one] using norm_exp_sub_partial_le x 2

theorem norm_exp_sub_quadratic_le (x : A) :
    ‖NormedSpace.exp x - (1 + x + (1 / 2 : ℝ) • x ^ 2)‖ ≤ ‖x‖ ^ 3 * Real.exp ‖x‖ := by
  convert norm_exp_sub_partial_le x 3 using 1; norm_num [sum_range_succ]

end PaperP1.BanachExponentialRemainder
