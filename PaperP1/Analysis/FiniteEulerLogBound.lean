module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # Exact finite Euler logarithms with explicit quadratic factor errors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteEulerLogBound
open Finset
open scoped Classical

def product {ι : Type*} (S : Finset ι) (z : ι → ℂ) : ℂ := ∏ i ∈ S, (1-z i)⁻¹

theorem factor_ne (z : ℂ) (hz : ‖z‖ ≤ 1/2) : 1-z ≠ 0 := by
  intro h
  have he : z=1 := (sub_eq_zero.mp h).symm
  rw [he,norm_one] at hz
  norm_num at hz

theorem point_log_error (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    |Real.log ‖(1-z)⁻¹‖-z.re| ≤ ‖z‖^2 := by
  have hlt : ‖z‖ < 1 := by linarith
  have ht := Complex.norm_log_one_sub_inv_sub_self_le hlt
  have hi : (1-‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : 0 < 1-‖z‖) (by norm_num : (0 : ℝ) < 2)]
    norm_num
    linarith
  have hb : ‖Complex.log (1-z)⁻¹-z‖ ≤ ‖z‖^2 := by
    calc
      _ ≤ ‖z‖^2*(1-‖z‖)⁻¹/2 := ht
      _ ≤ ‖z‖^2*2/2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hr := (Complex.abs_re_le_norm (Complex.log (1-z)⁻¹-z)).trans hb
  simpa only [Complex.sub_re,Complex.log_re] using hr

theorem product_ne {ι : Type*} (S : Finset ι) (z : ι → ℂ) (hz : ∀ i ∈ S, ‖z i‖ ≤ 1/2) :
    product S z ≠ 0 := prod_ne_zero_iff.mpr (fun i hi ↦ inv_ne_zero (factor_ne (z i) (hz i hi)))

theorem log_product_exact {ι : Type*} (S : Finset ι) (z : ι → ℂ) (hz : ∀ i ∈ S, ‖z i‖ ≤ 1/2) :
    Real.log ‖product S z‖=∑ i ∈ S, Real.log ‖(1-z i)⁻¹‖ := by
  rw [product,norm_prod,Real.log_prod]
  intro i hi
  exact norm_ne_zero_iff.mpr (inv_ne_zero (factor_ne (z i) (hz i hi)))

theorem log_product_error {ι : Type*} (S : Finset ι) (z : ι → ℂ) (hz : ∀ i ∈ S, ‖z i‖ ≤ 1/2) :
    |Real.log ‖product S z‖-(∑ i ∈ S, (z i).re)| ≤ ∑ i ∈ S, ‖z i‖^2 := by
  rw [log_product_exact S z hz,← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i hi ↦ point_log_error (z i) (hz i hi)))

theorem norm_product_bound {ι : Type*} (S : Finset ι) (z : ι → ℂ) (hz : ∀ i ∈ S, ‖z i‖ ≤ 1/2) :
    ‖product S z‖ ≤ Real.exp ((∑ i ∈ S, (z i).re)+(∑ i ∈ S, ‖z i‖^2)) := by
  have hh := (abs_le.mp (log_product_error S z hz)).2
  have hl : Real.log ‖product S z‖ ≤ (∑ i ∈ S, (z i).re)+(∑ i ∈ S, ‖z i‖^2) := by linarith
  have he := Real.exp_le_exp.mpr hl
  rwa [Real.exp_log (norm_pos_iff.mpr (product_ne S z hz))] at he
end FiniteEulerLogBound
