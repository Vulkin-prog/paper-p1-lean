module

public import PaperP1.Model.TouchardCountMoments

/-! # A finite transfer of exact quadratic factorial corrections to the genuine second derivative of the Touchard polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TouchardApproximation

open Finset PaperP1.TouchardCountMoments

theorem finite_bound (r : ℕ) (m : ℕ → ℝ) (μ a τ : ℝ)
    (h : ∀ j ∈ range (r + 1), |m j - μ ^ j - (j.choose 2 : ℝ) * μ ^ (j - 2) * a| ≤ τ) :
    |(∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ) * m j) - (touchard r).eval μ -
      a / 2 * ((touchard r).derivative.derivative).eval μ| ≤
        (∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ)) * τ := by
  have hcorr : a / 2 * ((touchard r).derivative.derivative).eval μ =
      a * ∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ) * (j.choose 2 : ℝ) * μ ^ (j - 2) := by
    rw [show a / 2 * ((touchard r).derivative.derivative).eval μ =
      a * (((touchard r).derivative.derivative).eval μ / 2) by ring, second_derivative]
  have hid : (∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ) * m j) - (touchard r).eval μ -
      a / 2 * ((touchard r).derivative.derivative).eval μ =
      ∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ) *
        (m j - μ ^ j - (j.choose 2 : ℝ) * μ ^ (j - 2) * a) := by
    rw [eval_touchard, hcorr, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [hid]
  apply (abs_sum_le_sum_abs _ _).trans
  rw [sum_mul]
  apply sum_le_sum
  intro j hj
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (h j hj) (Nat.cast_nonneg _)

end PaperP1.TouchardApproximation
