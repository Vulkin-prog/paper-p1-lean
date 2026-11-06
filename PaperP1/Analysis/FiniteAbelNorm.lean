module

public import PaperP1.Analysis.FiniteGramLargeValues
public import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FiniteAbelNorm
open Finset PaperP1
open scoped Classical

def partialSum (a : ℕ → ℂ) (L : ℕ) : ℂ := ∑ i ∈ range L, a i

theorem partialSum_succ (a : ℕ → ℂ) (L : ℕ) : partialSum a (L+1)=partialSum a L+a L := sum_range_succ a L

theorem finite_identity (L : ℕ) (a w : ℕ → ℂ) :
    (∑ i ∈ range L, a i*w i)=partialSum a L*w L+
      ∑ k ∈ range L, partialSum a (k+1)*(w k-w (k+1)) := by
  induction L with
  | zero => simp [partialSum]
  | succ L ih =>
    rw [sum_range_succ,ih,sum_range_succ]
    simp only [partialSum_succ a L]
    ring

theorem telescoping (L : ℕ) (w : ℕ → ℝ) :
    (∑ k ∈ range L, (w k-w (k+1)))=w 0-w L := by
  induction L with
  | zero => simp
  | succ L ih => rw [sum_range_succ,ih]; ring

theorem norm_bound (L : ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ) (D : ℝ)
    (hpartialSum : ∀ k ≤ L, ‖partialSum a k‖ ≤ D)
    (hw : ∀ k ≤ L, 0 ≤ w k) (hmono : ∀ k < L, w (k+1) ≤ w k) :
    ‖∑ i ∈ range L, a i*(w i : ℂ)‖ ≤ D*w 0 := by
  have hboundary : ‖partialSum a L*(w L : ℂ)‖ ≤ D*w L := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw L le_rfl)]
    exact mul_le_mul_of_nonneg_right (hpartialSum L le_rfl) (hw L le_rfl)
  have hterms (k : ℕ) (hk : k ∈ range L) :
      ‖partialSum a (k+1)*((w k : ℂ)-(w (k+1) : ℂ))‖ ≤ D*(w k-w (k+1)) := by
    have hkL := mem_range.mp hk
    have hd : 0 ≤ w k-w (k+1) := sub_nonneg.mpr (hmono k hkL)
    rw [← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_right (hpartialSum (k+1) (by omega)) hd
  rw [finite_identity]
  calc
    _ ≤ ‖partialSum a L*(w L : ℂ)‖+‖∑ k ∈ range L, partialSum a (k+1)*((w k : ℂ)-(w (k+1) : ℂ))‖ := norm_add_le _ _
    _ ≤ D*w L+(∑ k ∈ range L, ‖partialSum a (k+1)*((w k : ℂ)-(w (k+1) : ℂ))‖) :=
      add_le_add hboundary (norm_sum_le _ _)
    _ ≤ D*w L+(∑ k ∈ range L, D*(w k-w (k+1))) := add_le_add le_rfl (sum_le_sum hterms)
    _ = _ := by rw [← mul_sum,telescoping]; ring

theorem reciprocal_norm_bound (N L : ℕ) (hN : 0 < N) (a : ℕ → ℂ) (D : ℝ)
    (hpartialSum : ∀ k ≤ L, ‖partialSum a k‖ ≤ D) :
    ‖∑ i ∈ range L, a i/((N+i : ℕ) : ℂ)‖ ≤ D/(N : ℝ) := by
  have hh := norm_bound L a (fun k ↦ 1/((N+k : ℕ) : ℝ)) D hpartialSum
    (fun k _hk ↦ by positivity) (by
      intro k hk
      have hp : (0 : ℝ) < (N+k : ℕ) := by exact_mod_cast (show 0 < N+k by omega)
      exact one_div_le_one_div_of_le hp (by exact_mod_cast (show N+k ≤ N+(k+1) by omega)))
  simpa [div_eq_mul_inv] using hh
end PaperP1.FiniteAbelNorm
