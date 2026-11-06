module

public import PaperP1.Analysis.FiniteAbelNorm

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FiniteAbelVariation
open Finset PaperP1
open scoped Classical

theorem norm_bound (L : ℕ) (a w : ℕ → ℂ) (D : ℝ)
    (hPartial : ∀ k ≤ L, ‖FiniteAbelNorm.partialSum a k‖ ≤ D) :
    ‖∑ i ∈ range L, a i*w i‖ ≤ D*(‖w L‖+∑ k ∈ range L, ‖w k-w (k+1)‖) := by
  have hBoundary : ‖FiniteAbelNorm.partialSum a L*w L‖ ≤ D*‖w L‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hPartial L le_rfl) (norm_nonneg _)
  have hTerms (k : ℕ) (hk : k ∈ range L) :
      ‖FiniteAbelNorm.partialSum a (k+1)*(w k-w (k+1))‖ ≤ D*‖w k-w (k+1)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hPartial (k+1) (by have hh := mem_range.mp hk; omega)) (norm_nonneg _)
  rw [FiniteAbelNorm.finite_identity]
  calc
    _ ≤ ‖FiniteAbelNorm.partialSum a L*w L‖+
        ‖∑ k ∈ range L, FiniteAbelNorm.partialSum a (k+1)*(w k-w (k+1))‖ := norm_add_le _ _
    _ ≤ D*‖w L‖+∑ k ∈ range L, ‖FiniteAbelNorm.partialSum a (k+1)*(w k-w (k+1))‖ :=
      add_le_add hBoundary (norm_sum_le _ _)
    _ ≤ D*‖w L‖+∑ k ∈ range L, D*‖w k-w (k+1)‖ := add_le_add le_rfl (sum_le_sum hTerms)
    _ = _ := by rw [← mul_sum]; ring

theorem real_norm_bound (L : ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ) (D : ℝ)
    (hPartial : ∀ k ≤ L, ‖FiniteAbelNorm.partialSum a k‖ ≤ D) :
    ‖∑ i ∈ range L, a i*(w i : ℂ)‖ ≤ D*(|w L|+∑ k ∈ range L, |w k-w (k+1)|) := by
  have hh := norm_bound L a (fun k ↦ (w k : ℂ)) D hPartial
  simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hh

theorem difference_bound (L : ℕ) (a w : ℕ → ℂ) (D M V : ℝ)
    (hPartial : ∀ k ≤ L, ‖FiniteAbelNorm.partialSum a k‖ ≤ D)
    (hLast : ‖w L‖ ≤ M) (hVariation : ∀ k < L, ‖w k-w (k+1)‖ ≤ V) :
    ‖∑ i ∈ range L, a i*w i‖ ≤ D*(M+(L : ℝ)*V) := by
  have hD : 0 ≤ D := by
    have hh := hPartial 0 (by omega)
    simpa only [FiniteAbelNorm.partialSum,range_zero,sum_empty,norm_zero] using hh
  have hSum : (∑ k ∈ range L, ‖w k-w (k+1)‖) ≤ (L : ℝ)*V := by
    have hh := sum_le_sum (s := range L) (fun k hk ↦ hVariation k (mem_range.mp hk))
    simpa only [sum_const,card_range,nsmul_eq_mul] using hh
  exact (norm_bound L a w D hPartial).trans
    (mul_le_mul_of_nonneg_left (add_le_add hLast hSum) hD)
end PaperP1.FiniteAbelVariation
