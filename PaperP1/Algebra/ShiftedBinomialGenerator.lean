module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring.Basic
public import Lean.Elab.Tactic.Omega

/-! # The exact weighted generator of a binomial pair contribution -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShiftedBinomialGenerator

open Finset

theorem finite_sum (n : ℕ) (hn : 2 ≤ n) (u p β : ℝ) :
    (∑ r ∈ range (n + 1), u ^ r * (if r < 2 then 0 else β * ((n - 2).choose (r - 2) : ℝ) * p ^ (r - 2))) =
      u ^ 2 * β * (1 + u * p) ^ (n - 2) := by
  let f := fun r : ℕ ↦ u ^ r * (if r < 2 then 0 else β * ((n - 2).choose (r - 2) : ℝ) * p ^ (r - 2))
  have hsmall : (∑ r ∈ range 2, f r) = 0 := by norm_num [f, sum_range_succ]
  have hshift (j : ℕ) : f (2 + j) = (u ^ 2 * β) * (((n - 2).choose j : ℝ) * (u * p) ^ j) := by
    dsimp only [f]
    rw [ite_eq_right (by omega : ¬2 + j < 2), show 2 + j - 2 = j by omega, pow_add, mul_pow]
    ring
  have hbinomial : (∑ j ∈ range (n - 2 + 1), ((n - 2).choose j : ℝ) * (u * p) ^ j) =
      (1 + u * p) ^ (n - 2) := by
    rw [add_comm (1 : ℝ), add_pow]
    apply sum_congr rfl
    intro j _hj
    simp only [one_pow, mul_one]
    ring
  change (∑ r ∈ range (n + 1), f r) = _
  rw [show n + 1 = 2 + (n - 2 + 1) by omega, sum_range_add, hsmall, zero_add]
  simp_rw [hshift]
  rw [← mul_sum, hbinomial]

end PaperP1.ShiftedBinomialGenerator
