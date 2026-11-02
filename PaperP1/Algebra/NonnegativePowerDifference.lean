module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity

/-! # Power stability on a bounded nonnegative interval -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.NonnegativePowerDifference

theorem bound (a b M : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ M) (hbM : b ≤ M) (r : ℕ) :
    |a ^ r - b ^ r| ≤ |a - b| * r * M ^ (r - 1) := by
  have h := abs_pow_sub_pow_le (a := a) (b := b) (n := r)
  rw [abs_of_nonneg ha, abs_of_nonneg hb] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (le_max_left a b |>.trans' ha) (max_le haM hbM) (r - 1)) (by positivity))

end PaperP1.NonnegativePowerDifference
