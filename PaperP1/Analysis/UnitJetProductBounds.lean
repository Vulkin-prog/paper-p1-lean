module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Explicit derivative bounds for products and powers of actual unit jets

Leibniz and the binomial theorem retain the number of factors to the derivative
order. Smoothness is needed only at the actual point under consideration.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitJetProductBounds

open Finset
open scoped ContDiff

theorem product_bound (f g : ℝ → ℝ) (x A B : ℝ) (hA : 0 ≤ A)
    (r j : ℕ) (hj : j ≤ r) (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hfj : ∀ k ≤ r, |iteratedDeriv k f x| ≤ A ^ k)
    (hgj : ∀ k ≤ r, |iteratedDeriv k g x| ≤ B ^ k) :
    |iteratedDeriv j (fun t ↦ f t * g t) x| ≤ (A + B) ^ j := by
  rw [iteratedDeriv_fun_mul (hf.of_le (by simp)) (hg.of_le (by simp))]
  calc
    _ ≤ ∑ k ∈ range (j + 1), |(j.choose k : ℝ) * iteratedDeriv k f x * iteratedDeriv (j - k) g x| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (j + 1), (j.choose k : ℝ) * A ^ k * B ^ (j - k) := by
      apply sum_le_sum
      intro k hk
      have hk' : k ≤ r := by have := mem_range.mp hk; omega
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfj k hk') (Nat.cast_nonneg _))
        (hgj (j - k) (by omega)) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hA _))
    _ = (A + B) ^ j := by
      rw [add_pow]
      apply sum_congr rfl
      intro k _hk
      ring

theorem power_bound (f : ℝ → ℝ) (x : ℝ) (r : ℕ) (hf : ContDiffAt ℝ ∞ f x)
    (hfj : ∀ j ≤ r, |iteratedDeriv j f x| ≤ 1) (m : ℕ) :
    ∀ j ≤ r, |iteratedDeriv j (fun t ↦ f t ^ m) x| ≤ (m : ℝ) ^ j := by
  induction m with
  | zero =>
    intro j _hj
    simp only [pow_zero, iteratedDeriv_const, Nat.cast_zero]
    split_ifs with hj
    · subst j
      norm_num
    · simp only [zero_pow hj, abs_zero, le_refl]
  | succ m ih =>
    intro j hj
    simp only [pow_succ]
    have hh := product_bound (fun t ↦ f t ^ m) f x (m : ℝ) 1 (Nat.cast_nonneg _)
      r j hj (hf.pow m) hf ih (fun k hk ↦ by simpa only [one_pow] using hfj k hk)
    simpa only [Nat.cast_add, Nat.cast_one] using hh

theorem two_powers_bound (f g : ℝ → ℝ) (x : ℝ) (r : ℕ)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hfj : ∀ j ≤ r, |iteratedDeriv j f x| ≤ 1)
    (hgj : ∀ j ≤ r, |iteratedDeriv j g x| ≤ 1) (a b j : ℕ) (hj : j ≤ r) :
    |iteratedDeriv j (fun t ↦ f t ^ a * g t ^ b) x| ≤ ((a + b : ℕ) : ℝ) ^ j := by
  have hh := product_bound (fun t ↦ f t ^ a) (fun t ↦ g t ^ b) x (a : ℝ) (b : ℝ)
    (Nat.cast_nonneg _) r j hj (hf.pow a) (hg.pow b)
    (power_bound f x r hf hfj a) (power_bound g x r hg hgj b)
  simpa only [Nat.cast_add] using hh

end PaperP1.UnitJetProductBounds
