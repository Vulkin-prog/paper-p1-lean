module

public import PaperP1.Asymptotics.QuadraticKernelExponents
public import Mathlib.Analysis.SpecialFunctions.Log.Basic


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.QuadraticComparisonRange
open PaperP1 QuadraticKernelExponents

theorem exponent_le_affine_iff_of_nonneg_delta (β δ : ℝ) (hδ : 0 ≤ δ) :
    exponent β δ ≤ affine β δ ↔ β-2*δ ≤ 2 := by
  constructor
  · intro h
    by_contra hRange
    have hBad : 2 < β-2*δ := lt_of_not_ge hRange
    have hMax : 1-β/2 ≤ β/2-δ := by linarith only [hBad,hδ]
    have hMin : β/2-δ ≤ β-δ := by linarith only [hBad,hδ]
    rw [exponent,max_eq_left hMax,min_eq_right hMin] at h
    unfold affine at h
    linarith only [h,hBad]
  · exact exponent_le_affine_of_range β δ

theorem range_not_necessary_without_nonnegative_delta :
    (-4 : ℝ) < 0 ∧ exponent (-4) (-4) ≤ affine (-4) (-4) ∧
      ¬((-4 : ℝ)-2*(-4) ≤ 2) := by
  norm_num [exponent,affine]

theorem actual_delta_nonneg (N e : ℕ) (hN : 2 ≤ N) (he : 0 < e) :
    0 ≤ Real.log (e : ℝ)/Real.log (N : ℝ) := by
  have hE : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hNR : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  exact div_nonneg (Real.log_nonneg hE) (Real.log_pos hNR).le

theorem actual_comparison_iff (N e : ℕ) (hN : 2 ≤ N) (he : 0 < e) (β : ℝ) :
    exponent β (Real.log (e : ℝ)/Real.log (N : ℝ)) ≤
      affine β (Real.log (e : ℝ)/Real.log (N : ℝ)) ↔
      β-2*(Real.log (e : ℝ)/Real.log (N : ℝ)) ≤ 2 :=
  exponent_le_affine_iff_of_nonneg_delta β _ (actual_delta_nonneg N e hN he)

end PaperP1.QuadraticComparisonRange
