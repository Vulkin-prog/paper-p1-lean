module

public import PaperP1.Algebra.IntegerPolynomialRootBound

@[expose] public section

/-!
# Integer square separation and polynomial evaluation

Elementary estimates used in the new algebraic proof of companion T1.1.
-/

namespace PaperP1.IntegerSquareGap

open Finset Polynomial

theorem abs_le_abs_sq_sub_sq {a b : ℤ} (hne : b ^ 2 ≠ a ^ 2) :
    |b| ≤ |b ^ 2 - a ^ 2| := by
  have hab : |a| ≠ |b| := by
    intro h
    apply hne
    have hs := congrArg (fun z : ℤ => z ^ 2) h
    simpa only [sq_abs] using hs.symm
  rcases lt_or_gt_of_ne hab with h | h
  · have hstep : |a| + 1 ≤ |b| := by omega
    have hprod : 0 ≤ (|b| - |a| - 1) * (|b| + |a|) :=
      mul_nonneg (by omega) (by positivity)
    have hbound : |b| ≤ b ^ 2 - a ^ 2 := by
      nlinarith [sq_abs a, sq_abs b, abs_nonneg a]
    exact hbound.trans (le_abs_self _)
  · have hstep : |b| + 1 ≤ |a| := by omega
    have hprod : 0 ≤ (|a| - |b| - 1) * (|a| + |b|) :=
      mul_nonneg (by omega) (by positivity)
    have hbound : |b| ≤ -(b ^ 2 - a ^ 2) := by
      nlinarith [sq_abs a, sq_abs b, abs_nonneg b]
    exact hbound.trans (neg_le_abs _)

theorem natAbs_le_natAbs_sq_sub_sq {a b : ℤ} (hne : b ^ 2 ≠ a ^ 2) :
    b.natAbs ≤ (b ^ 2 - a ^ 2).natAbs := by
  have h := abs_le_abs_sq_sub_sq hne
  simpa only [Int.abs_eq_natAbs, Nat.cast_le] using h

theorem eval_natAbs_le
    (p : ℤ[X]) {n U : ℕ} (hn : p.natDegree ≤ n) (hU : 1 ≤ U) :
    (p.eval (U : ℤ)).natAbs ≤
      (n + 1) * integerPolynomialHeight p * U ^ n := by
  rw [Polynomial.eval_eq_sum_range' (show p.natDegree < n + 1 by omega)]
  calc
    _ ≤ ∑ i ∈ range (n + 1), (p.coeff i * (U : ℤ) ^ i).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _i ∈ range (n + 1), integerPolynomialHeight p * U ^ n := by
      apply sum_le_sum
      intro i hi
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      exact Nat.mul_le_mul (coeff_natAbs_le_integerPolynomialHeight p i)
        (Nat.pow_le_pow_right hU (by simpa only [mem_range, Nat.lt_succ_iff] using hi))
    _ = (n + 1) * integerPolynomialHeight p * U ^ n := by
      simp [mul_assoc]

end PaperP1.IntegerSquareGap

