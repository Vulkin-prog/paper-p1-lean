module

public import PaperP1.Analysis.FiniteEulerLogBound
public import PaperP1.Analysis.LogarithmicPhase

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RealUnitEulerComparison
open Finset PaperP1
open scoped Classical

theorem unit_real_part_bound (f : ℝ) (hf : |f| ≤ 1) (z : ℂ) (hz : ‖z‖=1) :
    4*f*z.re ≤ 3+(z^2).re := by
  have hUnit := Complex.sq_norm z
  rw [hz] at hUnit
  simp only [one_pow,Complex.normSq_apply] at hUnit
  have hfBounds := abs_le.mp hf
  have hfSquare : f^2 ≤ 1 := by
    have hh := mul_nonneg (sub_nonneg.mpr hfBounds.2) (show 0 ≤ 1+f by linarith only [hfBounds.1])
    nlinarith only [hh]
  simp only [pow_two,Complex.mul_re]
  nlinarith only [hUnit,hfSquare,sq_nonneg (z.re-f)]

theorem coefficient_norm_bound (f w : ℝ) (hf : |f| ≤ 1) (hw : 0 ≤ w)
    (z : ℂ) (hz : ‖z‖=1) : ‖(f : ℂ)*(w : ℂ)*z‖ ≤ w := by
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg hw,hz,mul_one]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hf hw

theorem fourth_power_bound {ι : Type*} (S : Finset ι) (f w : ι → ℝ) (z : ι → ℂ)
    (hf : ∀ i ∈ S, |f i| ≤ 1) (hw : ∀ i ∈ S, 0 ≤ w i ∧ w i ≤ 1/2)
    (hz : ∀ i ∈ S, ‖z i‖=1) :
    ‖FiniteEulerLogBound.product S (fun i ↦ (f i : ℂ)*(w i : ℂ)*z i)‖^4 ≤
      Real.exp (8*(∑ i ∈ S, (w i)^2))*
        ‖FiniteEulerLogBound.product S (fun i ↦ (w i : ℂ))‖^3*
        ‖FiniteEulerLogBound.product S (fun i ↦ (w i : ℂ)*(z i)^2)‖ := by
  let A := fun i ↦ (f i : ℂ)*(w i : ℂ)*z i
  let B := fun i ↦ (w i : ℂ)
  let C := fun i ↦ (w i : ℂ)*(z i)^2
  let E : ℝ := ∑ i ∈ S, (w i)^2
  have hANorm : ∀ i ∈ S, ‖A i‖ ≤ w i := fun i hi ↦ coefficient_norm_bound _ _ (hf i hi) (hw i hi).1 _ (hz i hi)
  have hBNorm : ∀ i ∈ S, ‖B i‖=w i := by
    intro i hi
    exact (Complex.norm_real _).trans ((Real.norm_eq_abs _).trans (abs_of_nonneg (hw i hi).1))
  have hCNorm : ∀ i ∈ S, ‖C i‖=w i := by
    intro i hi
    simp only [C,norm_mul,norm_pow,hz i hi,one_pow,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (hw i hi).1]
  have hAHalf : ∀ i ∈ S, ‖A i‖ ≤ 1/2 := fun i hi ↦ (hANorm i hi).trans (hw i hi).2
  have hBHalf : ∀ i ∈ S, ‖B i‖ ≤ 1/2 := fun i hi ↦ (hBNorm i hi).le.trans (hw i hi).2
  have hCHalf : ∀ i ∈ S, ‖C i‖ ≤ 1/2 := fun i hi ↦ (hCNorm i hi).le.trans (hw i hi).2
  have hASquare : (∑ i ∈ S, ‖A i‖^2) ≤ E := by
    apply sum_le_sum
    intro i hi
    exact pow_le_pow_left₀ (norm_nonneg _) (hANorm i hi) 2
  have hBSquare : (∑ i ∈ S, ‖B i‖^2)=E := sum_congr rfl (fun i hi ↦ by rw [hBNorm i hi])
  have hCSquare : (∑ i ∈ S, ‖C i‖^2)=E := sum_congr rfl (fun i hi ↦ by rw [hCNorm i hi])
  have hA := (abs_le.mp (FiniteEulerLogBound.log_product_error S A hAHalf)).2
  have hB := (abs_le.mp (FiniteEulerLogBound.log_product_error S B hBHalf)).1
  have hC := (abs_le.mp (FiniteEulerLogBound.log_product_error S C hCHalf)).1
  rw [hBSquare] at hB
  rw [hCSquare] at hC
  have hPoint : 4*(∑ i ∈ S, (A i).re) ≤ 3*(∑ i ∈ S, (B i).re)+(∑ i ∈ S, (C i).re) := by
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    have hh := mul_le_mul_of_nonneg_left (unit_real_part_bound (f i) (hf i hi) (z i) (hz i hi)) (hw i hi).1
    dsimp only [A,B,C]
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    nlinarith only [hh]
  have hLog : 4*Real.log ‖FiniteEulerLogBound.product S A‖ ≤
      8*E+3*Real.log ‖FiniteEulerLogBound.product S B‖+Real.log ‖FiniteEulerLogBound.product S C‖ := by
    linarith only [hA,hB,hC,hASquare,hPoint]
  have hAP := norm_pos_iff.mpr (FiniteEulerLogBound.product_ne S A hAHalf)
  have hBP := norm_pos_iff.mpr (FiniteEulerLogBound.product_ne S B hBHalf)
  have hCP := norm_pos_iff.mpr (FiniteEulerLogBound.product_ne S C hCHalf)
  have hExp := Real.exp_le_exp.mpr hLog
  rw [show (4 : ℝ)=((4 : ℕ) : ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log hAP,
    Real.exp_add,Real.exp_add,show (3 : ℝ)=((3 : ℕ) : ℝ) by norm_num,
    Real.exp_nat_mul,Real.exp_log hBP,Real.exp_log hCP] at hExp
  exact hExp

theorem stronger_scalar_comparison_fails :
    ¬(∀ x : ℝ, -1 ≤ x → x ≤ 1 → 2*|x| ≤ 1+(2*x^2-1)) := by
  intro h
  have hh := h (1/2) (by norm_num) (by norm_num)
  norm_num at hh
end PaperP1.RealUnitEulerComparison
