module

public import PaperP1.Algebra.PolynomialHeightArithmetic
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Explicit growth of an integer polynomial from its nonzero integral leading coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerPolynomialGrowth

open Polynomial Finset

theorem lower_power_bound (P : ℤ[X]) (a M : ℕ) (ha : 0 < a) (hdeg : P.natDegree = a)
    (hcoeff : ∀ n, (P.coeff n).natAbs ≤ M) (x : ℤ) (hx : 1 ≤ x.natAbs) :
    x.natAbs ^ a ≤ (P.eval x).natAbs + a * M * x.natAbs ^ (a - 1) := by
  have hp0 : P ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hdeg
    omega
  have hlc : 1 ≤ P.leadingCoeff.natAbs := Nat.one_le_iff_ne_zero.mpr
    (Int.natAbs_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp0))
  let T : ℤ := ∑ k ∈ range a, P.coeff k * x ^ k
  have heval : P.eval x = T + P.leadingCoeff * x ^ a := by
    rw [eval_eq_sum_range, hdeg, sum_range_succ]
    change _ = T + P.coeff P.natDegree * x ^ a
    rw [hdeg]
  have htail : T.natAbs ≤ a * M * x.natAbs ^ (a - 1) := by
    calc
      T.natAbs ≤ ∑ k ∈ range a, (P.coeff k * x ^ k).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _k ∈ range a, M * x.natAbs ^ (a - 1) := by
        apply sum_le_sum
        intro k hk
        rw [Int.natAbs_mul, Int.natAbs_pow]
        exact Nat.mul_le_mul (hcoeff k) (Nat.pow_le_pow_right hx (by have := mem_range.mp hk; omega))
      _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_id]; ring
  have hlead : (P.leadingCoeff * x ^ a).natAbs ≤ (P.eval x).natAbs + T.natAbs := by
    have he : P.leadingCoeff * x ^ a = P.eval x - T := by rw [heval]; ring
    rw [he, sub_eq_add_neg]
    simpa only [Int.natAbs_neg] using Int.natAbs_add_le (P.eval x) (-T)
  calc
    x.natAbs ^ a ≤ P.leadingCoeff.natAbs * x.natAbs ^ a := by
      simpa only [one_mul] using Nat.mul_le_mul_right (x.natAbs ^ a) hlc
    _ = (P.leadingCoeff * x ^ a).natAbs := by rw [Int.natAbs_mul, Int.natAbs_pow]
    _ ≤ (P.eval x).natAbs + a * M * x.natAbs ^ (a - 1) :=
      hlead.trans (Nat.add_le_add_left htail _)

end PaperP1.IntegerPolynomialGrowth
