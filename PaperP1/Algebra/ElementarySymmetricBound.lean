module

public import PaperP1.Algebra.SubsetPowerSums
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # An all-order elementary-symmetric bound for nonnegative heterogeneous weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ElementarySymmetricBound

open Finset PaperP1.SubsetPowerSums

theorem power_add_linear_lower (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℕ) :
    a ^ (r + 1) + (r + 1 : ℕ) * b * a ^ r ≤ (a + b) ^ (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp := mul_le_mul_of_nonneg_right ih (add_nonneg ha hb)
    have hn : 0 ≤ ((r + 1 : ℕ) : ℝ) * b ^ 2 * a ^ r := by positivity
    simp only [pow_succ] at hp ⊢
    push_cast at hp hn ⊢
    nlinarith only [hp, hn]

theorem factorial_elementary_le {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (hp : ∀ x, 0 ≤ p x) (G : Finset ι) (r : ℕ) :
    (r.factorial : ℝ) * elementary p G r ≤ (∑ x ∈ G, p x) ^ r := by
  induction G using Finset.induction_on generalizing r with
  | empty =>
    cases r with
    | zero => simp only [elementary_zero, Nat.factorial_zero, Nat.cast_one, mul_one, pow_zero, le_refl]
    | succ r => simp [elementary, powersetCard_eq_empty.mpr (by simp : (∅ : Finset ι).card < r + 1)]
  | @insert x G hx ih =>
    cases r with
    | zero => simp only [elementary_zero, Nat.factorial_zero, Nat.cast_one, mul_one, pow_zero, le_refl]
    | succ r =>
      rw [elementary_insert p G x hx r, sum_insert hx]
      have hsecond := mul_le_mul_of_nonneg_left (ih r)
        (mul_nonneg (Nat.cast_nonneg (r + 1)) (hp x))
      have hsum : 0 ≤ ∑ y ∈ G, p y := sum_nonneg fun y _ ↦ hp y
      calc
        _ = ((r + 1).factorial : ℝ) * elementary p G (r + 1) +
            ((r + 1 : ℕ) : ℝ) * p x * ((r.factorial : ℝ) * elementary p G r) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ ≤ (∑ y ∈ G, p y) ^ (r + 1) + ((r + 1 : ℕ) : ℝ) * p x * (∑ y ∈ G, p y) ^ r :=
          add_le_add (ih (r + 1)) hsecond
        _ ≤ (p x + ∑ y ∈ G, p y) ^ (r + 1) := by
          simpa only [add_comm] using power_add_linear_lower (∑ y ∈ G, p y) (p x) hsum (hp x) r

theorem elementary_le_power_div {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (hp : ∀ x, 0 ≤ p x) (G : Finset ι) (r : ℕ) :
    elementary p G r ≤ (∑ x ∈ G, p x) ^ r / (r.factorial : ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast Nat.factorial_pos r : (0 : ℝ) < r.factorial)).mpr
  simpa only [mul_comm] using factorial_elementary_le p hp G r

end PaperP1.ElementarySymmetricBound
