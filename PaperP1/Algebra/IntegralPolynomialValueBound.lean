module

public import PaperP1.Algebra.PolynomialHeightArithmetic

/-! # A nonconstant integer polynomial of bounded coefficient height can take a bounded value only at bounded integers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralPolynomialValueBound

open Polynomial PaperP1.PolynomialHeightArithmetic

theorem shifted_height (q : ℤ[X]) (M K : ℕ) (z : ℤ)
    (hq : ∀ n, (q.coeff n).natAbs ≤ M) (hz : z.natAbs ≤ K) :
    integerPolynomialHeight (q - C z) ≤ M + K := by
  apply integer_height_le
  intro n
  have hc : ((C z : ℤ[X]).coeff n).natAbs ≤ K := by
    by_cases hn : n = 0
    · simpa only [coeff_C, hn, ite_true] using hz
    · simp only [coeff_C, hn, ite_false, Int.natAbs_zero, Nat.zero_le]
  rw [coeff_sub, sub_eq_add_neg]
  exact (Int.natAbs_add_le _ _).trans (by
    rw [Int.natAbs_neg]
    exact Nat.add_le_add (hq n) hc)

theorem bounded_value (q : ℤ[X]) (hqdeg : 0 < q.natDegree) (M K : ℕ) (x : ℤ)
    (hq : ∀ n, (q.coeff n).natAbs ≤ M) (hvalue : (q.eval x).natAbs ≤ K) : x.natAbs ≤ M + K := by
  have hn : q - C (q.eval x) ≠ 0 := by
    intro hz
    have he := sub_eq_zero.mp hz
    rw [he, natDegree_C] at hqdeg
    exact Nat.lt_irrefl 0 hqdeg
  have hr : (q - C (q.eval x)).IsRoot x := by simp only [IsRoot.def, eval_sub, eval_C, sub_self]
  exact (PaperP1.integerRoot_natAbs_le_height hn hr).trans (shifted_height q M K (q.eval x) hq hvalue)

end PaperP1.IntegralPolynomialValueBound
