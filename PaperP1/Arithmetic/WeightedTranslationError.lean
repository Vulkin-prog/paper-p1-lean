module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Ring

/-! # Summing a uniform translation error preserves signed cancellation in the main term -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.WeightedTranslationError

open Finset

theorem weighted_error {ι : Type*} (S : Finset ι) (w σ T : ι → ℚ) (Q E : ℚ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hσ : ∀ i ∈ S, |σ i| ≤ 1)
    (hT : ∀ i ∈ S, |T i - Q| ≤ E) :
    |(∑ i ∈ S, w i * σ i * T i) - Q * ∑ i ∈ S, w i * σ i| ≤ E * ∑ i ∈ S, w i := by
  calc
    _ = |∑ i ∈ S, w i * σ i * (T i - Q)| := by
      rw [mul_sum, ← sum_sub_distrib]
      congr 1
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ S, |w i * σ i * (T i - Q)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, E * w i := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (hw i hi)]
      calc
        _ ≤ w i * 1 * |T i - Q| := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hσ i hi) (hw i hi)) (abs_nonneg _)
        _ ≤ w i * E := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hT i hi) (hw i hi)
        _ = _ := mul_comm _ _
    _ = _ := (mul_sum S (fun i ↦ w i) E).symm

end PaperP1.WeightedTranslationError
