module

public import PaperP1.Analysis.BanachExponentialRemainder
public import Mathlib.Data.Nat.Choose.Basic

/-! # A factorial-denominator remainder for the Banach algebra exponential -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BanachFactorialRemainder

open Finset

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

omit [CompleteSpace A] in
theorem norm_tail_term_le (x : A) (n j : ℕ) :
    ‖(((j + n).factorial : ℝ)⁻¹) • x ^ (j + n)‖ ≤
      (‖x‖ ^ n / (n.factorial : ℝ)) * (‖x‖ ^ j / (j.factorial : ℝ)) := by
  have hf : (n.factorial : ℝ) * (j.factorial : ℝ) ≤ ((j + n).factorial : ℝ) := by
    have h := Nat.le_of_dvd (Nat.factorial_pos (j + n)) (Nat.factorial_mul_factorial_dvd_factorial_add j n)
    exact_mod_cast (show n.factorial * j.factorial ≤ (j + n).factorial by simpa only [Nat.mul_comm] using h)
  calc
    _ ≤ ‖x‖ ^ (j + n) / ((j + n).factorial : ℝ) := BanachExponentialRemainder.norm_term_le x (j + n)
    _ ≤ ‖x‖ ^ (j + n) / ((n.factorial : ℝ) * (j.factorial : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hf
    _ = _ := by rw [pow_add]; ring

theorem norm_exp_sub_partial_le (x : A) (n : ℕ) :
    ‖NormedSpace.exp x - ∑ j ∈ range n, ((j.factorial : ℝ)⁻¹) • x ^ j‖ ≤
      (‖x‖ ^ n / (n.factorial : ℝ)) * Real.exp ‖x‖ := by
  have ht := (hasSum_nat_add_iff' n).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have hr := (NormedSpace.expSeries_div_hasSum_exp ‖x‖).mul_left (‖x‖ ^ n / (n.factorial : ℝ))
  rw [← Real.exp_eq_exp_ℝ] at hr
  exact ht.norm_le_of_bounded hr (norm_tail_term_le x n)

end PaperP1.BanachFactorialRemainder
