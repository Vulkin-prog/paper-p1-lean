module

public import PaperP1.Arithmetic.ReciprocalOddPivots
public import PaperP1.Analysis.ClippedPowerSum

/-! # A uniform, finite large-square-part tail

This proves the positive-summation tail in the square-part reduction
without assuming any reciprocal-prime asymptotic.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReciprocalPivotSquareTail

open Finset PaperP1.ReciprocalOddPivots

def squareTail (X A : ℕ) : ℝ :=
  ∑ a ∈ (Icc 1 (Nat.sqrt X)).filter (A < ·), primeSum (X / a ^ 2)

theorem squareTail_nonneg (X A : ℕ) : 0 ≤ squareTail X A :=
  sum_nonneg (fun _ _ ↦ primeSum_nonneg _)

theorem term_bound (X a : ℕ) :
    primeSum (X / a ^ 2) ≤ (X : ℝ) * (a : ℝ) ^ (-(2 : ℝ)) := by
  calc
    _ ≤ ((X / a ^ 2 : ℕ) : ℝ) := primeSum_le _
    _ ≤ (X : ℝ) / (a ^ 2 : ℕ) := Nat.cast_div_le
    _ = _ := by rw [Nat.cast_pow, div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg a),
      Real.rpow_two]

theorem squareTail_bound (X A : ℕ) (hA : 1 ≤ A) :
    squareTail X A ≤ 2 * (X : ℝ) / A := by
  let S := (Icc 1 (Nat.sqrt X)).filter (A < ·)
  have htail := ClippedPowerSum.finite_tail_le_power S 2 (A : ℝ) (by norm_num)
    (by exact_mod_cast hA) (fun a ha ↦ by exact_mod_cast (mem_filter.mp ha).2)
  have htail' : (∑ a ∈ S, (a : ℝ) ^ (-(2 : ℝ))) ≤ 2 / (A : ℝ) := by
    convert htail using 1
    norm_num [PowerSeriesTail.constant, Real.rpow_neg_one, div_eq_mul_inv]
  calc
    _ ≤ ∑ a ∈ S, (X : ℝ) * (a : ℝ) ^ (-(2 : ℝ)) :=
      sum_le_sum (fun a _ ↦ term_bound X a)
    _ = (X : ℝ) * ∑ a ∈ S, (a : ℝ) ^ (-(2 : ℝ)) := (mul_sum _ _ _).symm
    _ ≤ (X : ℝ) * (2 / (A : ℝ)) := mul_le_mul_of_nonneg_left htail' (Nat.cast_nonneg X)
    _ = _ := by ring

theorem split_square_parts (X A : ℕ) :
    (∑ a ∈ Icc 1 (Nat.sqrt X), primeSum (X / a ^ 2)) =
      (∑ a ∈ (Icc 1 (Nat.sqrt X)).filter (· ≤ A), primeSum (X / a ^ 2)) +
      squareTail X A := by
  simpa only [squareTail, not_le] using
    (sum_filter_add_sum_filter_not (Icc 1 (Nat.sqrt X)) (· ≤ A)
      (fun a ↦ primeSum (X / a ^ 2))).symm

theorem full_square_part_bound (X A : ℕ) (hA : 1 ≤ A) :
    pivotSum X ≤
      (∑ a ∈ (Icc 1 (Nat.sqrt X)).filter (· ≤ A), primeSum (X / a ^ 2)) +
      2 * (X : ℝ) / A := by
  calc
    _ ≤ _ := square_part_reduction X
    _ = _ := split_square_parts X A
    _ ≤ _ := add_le_add le_rfl (squareTail_bound X A hA)

end PaperP1.ReciprocalPivotSquareTail
