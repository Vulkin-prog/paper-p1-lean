module

public import PaperP1.Algebra.CommonLinearNormalization
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs

/-! # The actual height cost of a bounded nonnegative integer linear coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerLinearFormHeight

theorem evaluation_bound (n B H : ℕ) (u : Fin n → ℕ) (hu : ∀ i, u i ≤ B)
    (v : Fin n → ℤ) (hv : ∀ i, (v i).natAbs ≤ H) :
    |MvPolynomial.eval v (CommonLinearNormalization.form (fun i ↦ (u i : ℤ)))| ≤ ((n * B * H : ℕ) : ℤ) := by
  classical
  rw [CommonLinearNormalization.evaluation]
  calc
    _ ≤ ∑ i, |(u i : ℤ) * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ((B * H : ℕ) : ℤ) := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul, Int.abs_natCast]
      have hvi : |v i| ≤ (H : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hv i
      have hui : (u i : ℤ) ≤ B := by exact_mod_cast hu i
      simpa only [Nat.cast_mul] using mul_le_mul hui hvi (abs_nonneg _) (Nat.cast_nonneg B)
    _ = _ := by simp [Nat.cast_mul, mul_assoc]

end PaperP1.IntegerLinearFormHeight
