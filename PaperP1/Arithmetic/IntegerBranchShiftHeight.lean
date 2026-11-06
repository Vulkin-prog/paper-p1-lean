module

public import PaperP1.Arithmetic.SplitRadicalPointHeight
public import Mathlib.Data.Int.Basic

/-! # A large integer branch shift forces any bounded divisible radical square to vanish -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerBranchShiftHeight
open Finset

theorem shift_bound (x w a : ℤ) (H : ℕ) (hH : 1 ≤ H)
    (hx : |x| ≤ (H : ℤ)) (hw : |w| ≤ (H : ℤ)) (hw0 : w ≠ 0) (hdiv : x + a ∣ w ^ 2) :
    |a| ≤ (2 * H ^ 2 : ℕ) := by
  have hle := Int.natAbs_le_of_dvd_ne_zero hdiv (pow_ne_zero 2 hw0)
  have hle' : |x + a| ≤ |w ^ 2| := by
    simpa only [Int.abs_eq_natAbs] using (by exact_mod_cast hle :
      ((x + a).natAbs : ℤ) ≤ (w ^ 2).natAbs)
  have hsq : |w ^ 2| ≤ (H : ℤ) ^ 2 := by
    rw [abs_pow]
    nlinarith [abs_nonneg w]
  have htri : |a| ≤ |x + a| + |x| := by
    have ht := abs_sub (x+a) x
    simpa only [add_sub_cancel_left] using ht
  have hHz : (1 : ℤ) ≤ H := by exact_mod_cast hH
  push_cast
  nlinarith

theorem large_shift_forces_zero (x w a : ℤ) (H : ℕ) (hH : 1 ≤ H)
    (hx : |x| ≤ (H : ℤ)) (hw : |w| ≤ (H : ℤ))
    (ha : (2 * H ^ 2 : ℕ) < |a|) (hdiv : x + a ∣ w ^ 2) : w = 0 := by
  by_contra hw0
  exact (not_lt_of_ge (shift_bound x w a H hH hx hw hw0 hdiv)) ha
end IntegerBranchShiftHeight
