module

public import PaperP1.Analysis.FiniteEulerLogBound
public import PaperP1.Analysis.RealUnitEulerComparison

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FiniteEulerDampingComparison
open Finset PaperP1
open scoped Classical

theorem real_projection_bound (f : ℝ) (hf : |f| ≤ 1) (z : ℂ) (hz : ‖z‖=1) :
    f*z.re ≤ 1 := by
  have hRe : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans_eq hz
  have hh := mul_le_mul hf hRe (abs_nonneg _) zero_le_one
  exact (le_abs_self (f*z.re)).trans (by simpa only [abs_mul,one_mul] using hh)

theorem coefficient_real_difference (f w v : ℝ) (hf : |f| ≤ 1) (hvw : v ≤ w)
    (z : ℂ) (hz : ‖z‖=1) :
    ((f : ℂ)*(w : ℂ)*z).re-((f : ℂ)*(v : ℂ)*z).re ≤ w-v := by
  have hh := mul_le_mul_of_nonneg_left (real_projection_bound f hf z hz) (sub_nonneg.mpr hvw)
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
  nlinarith only [hh]

theorem log_product_comparison {ι : Type*} (S : Finset ι) (f w v : ι → ℝ) (z : ι → ℂ)
    (hf : ∀ i ∈ S, |f i| ≤ 1)
    (hw : ∀ i ∈ S, 0 ≤ v i ∧ v i ≤ w i ∧ w i ≤ 1/2)
    (hz : ∀ i ∈ S, ‖z i‖=1) :
    Real.log ‖FiniteEulerLogBound.product S (fun i ↦ (f i : ℂ)*(w i : ℂ)*z i)‖ ≤
      Real.log ‖FiniteEulerLogBound.product S (fun i ↦ (f i : ℂ)*(v i : ℂ)*z i)‖+
        (∑ i ∈ S, (w i-v i))+2*(∑ i ∈ S, (w i)^2) := by
  let A := fun i ↦ (f i : ℂ)*(w i : ℂ)*z i
  let B := fun i ↦ (f i : ℂ)*(v i : ℂ)*z i
  let E : ℝ := ∑ i ∈ S, (w i)^2
  have hANorm : ∀ i ∈ S, ‖A i‖ ≤ w i := fun i hi ↦
    RealUnitEulerComparison.coefficient_norm_bound _ _ (hf i hi)
      ((hw i hi).1.trans (hw i hi).2.1) _ (hz i hi)
  have hBNorm : ∀ i ∈ S, ‖B i‖ ≤ v i := fun i hi ↦
    RealUnitEulerComparison.coefficient_norm_bound _ _ (hf i hi) (hw i hi).1 _ (hz i hi)
  have hAHalf : ∀ i ∈ S, ‖A i‖ ≤ 1/2 := fun i hi ↦ (hANorm i hi).trans (hw i hi).2.2
  have hBHalf : ∀ i ∈ S, ‖B i‖ ≤ 1/2 := fun i hi ↦
    (hBNorm i hi).trans ((hw i hi).2.1.trans (hw i hi).2.2)
  have hASquare : (∑ i ∈ S, ‖A i‖^2) ≤ E := by
    apply sum_le_sum
    intro i hi
    exact pow_le_pow_left₀ (norm_nonneg _) (hANorm i hi) 2
  have hBSquare : (∑ i ∈ S, ‖B i‖^2) ≤ E := by
    apply sum_le_sum
    intro i hi
    exact pow_le_pow_left₀ (norm_nonneg _) ((hBNorm i hi).trans (hw i hi).2.1) 2
  have hA := (abs_le.mp (FiniteEulerLogBound.log_product_error S A hAHalf)).2
  have hB := (abs_le.mp (FiniteEulerLogBound.log_product_error S B hBHalf)).1
  have hDifference : (∑ i ∈ S, (A i).re)-(∑ i ∈ S, (B i).re) ≤ ∑ i ∈ S, (w i-v i) := by
    rw [← sum_sub_distrib]
    exact sum_le_sum (fun i hi ↦ coefficient_real_difference _ _ _ (hf i hi) (hw i hi).2.1 _ (hz i hi))
  linarith only [hA,hB,hASquare,hBSquare,hDifference]

theorem norm_product_comparison {ι : Type*} (S : Finset ι) (f w v : ι → ℝ) (z : ι → ℂ)
    (hf : ∀ i ∈ S, |f i| ≤ 1)
    (hw : ∀ i ∈ S, 0 ≤ v i ∧ v i ≤ w i ∧ w i ≤ 1/2)
    (hz : ∀ i ∈ S, ‖z i‖=1) :
    ‖FiniteEulerLogBound.product S (fun i ↦ (f i : ℂ)*(w i : ℂ)*z i)‖ ≤
      Real.exp ((∑ i ∈ S, (w i-v i))+2*(∑ i ∈ S, (w i)^2))*
        ‖FiniteEulerLogBound.product S (fun i ↦ (f i : ℂ)*(v i : ℂ)*z i)‖ := by
  have hHalfW : ∀ i ∈ S, ‖(f i : ℂ)*(w i : ℂ)*z i‖ ≤ 1/2 := fun i hi ↦
    (RealUnitEulerComparison.coefficient_norm_bound _ _ (hf i hi)
      ((hw i hi).1.trans (hw i hi).2.1) _ (hz i hi)).trans (hw i hi).2.2
  have hHalfV : ∀ i ∈ S, ‖(f i : ℂ)*(v i : ℂ)*z i‖ ≤ 1/2 := fun i hi ↦
    (RealUnitEulerComparison.coefficient_norm_bound _ _ (hf i hi) (hw i hi).1 _ (hz i hi)).trans
      ((hw i hi).2.1.trans (hw i hi).2.2)
  have hAP := norm_pos_iff.mpr (FiniteEulerLogBound.product_ne S _ hHalfW)
  have hBP := norm_pos_iff.mpr (FiniteEulerLogBound.product_ne S _ hHalfV)
  have hh := Real.exp_le_exp.mpr (log_product_comparison S f w v z hf hw hz)
  rw [Real.exp_log hAP,Real.exp_add,Real.exp_add,Real.exp_log hBP] at hh
  exact hh.trans_eq (by rw [Real.exp_add]; ring)
end PaperP1.FiniteEulerDampingComparison
