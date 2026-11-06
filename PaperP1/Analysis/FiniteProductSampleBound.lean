module

public import PaperP1.Analysis.FiniteFibreSquareBudget

set_option autoImplicit false
@[expose] public noncomputable section
universe u836 v836
namespace PaperP1.FiniteProductSampleBound
open Finset PaperP1
open scoped Classical

theorem bound {ι : Type u836} {κ : Type v836} (J : Finset ι) (R : Finset κ)
    (A F : ι → κ → ℂ) (V C : ℝ)
    (hA : ∀ j ∈ J, ∀ r ∈ R, ‖A j r‖ ≤ V)
    (hF : ∀ j ∈ J, (∑ r ∈ R, ‖F j r‖^2) ≤ C) :
    (∑ r ∈ R, ‖∑ j ∈ J, A j r*F j r‖^2) ≤ (J.card : ℝ)^2*V^2*C := by
  have hPoint (r : κ) (hr : r ∈ R) :
      ‖∑ j ∈ J, A j r*F j r‖^2 ≤ (J.card : ℝ)*∑ j ∈ J, V^2*‖F j r‖^2 := by
    have hh := FiniteFibreSquareBudget.norm_sum_sq_le_card J (fun j ↦ A j r*F j r)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg J.card)
    apply sum_le_sum
    intro j hj
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hA j hj r hr) 2) (sq_nonneg _)
  calc
    _ ≤ ∑ r ∈ R, (J.card : ℝ)*∑ j ∈ J, V^2*‖F j r‖^2 := sum_le_sum hPoint
    _ = (J.card : ℝ)*V^2*∑ j ∈ J, ∑ r ∈ R, ‖F j r‖^2 := by
      rw [← mul_sum,sum_comm]
      simp only [← mul_sum]
      ring
    _ ≤ (J.card : ℝ)*V^2*∑ _j ∈ J, C :=
      mul_le_mul_of_nonneg_left (sum_le_sum hF) (by positivity)
    _ = _ := by simp; ring
end PaperP1.FiniteProductSampleBound
