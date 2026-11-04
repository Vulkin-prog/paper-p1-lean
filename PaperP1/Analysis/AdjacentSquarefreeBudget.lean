module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # An explicit reciprocal-square budget for the adjacent-squarefree source audit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AdjacentSquarefreeBudget

open Finset

theorem odd_term_bound (x : ℝ) (hx : 0 ≤ x) :
    1 / (2 * x + 3) ^ 2 ≤ 1 / (4 * (x + 1) * (x + 2)) := by
  apply one_div_le_one_div_of_le (by positivity : 0 < 4 * (x + 1) * (x + 2))
  nlinarith

theorem odd_partial_sum (J : ℕ) :
    (∑ j ∈ range (J + 1), 1 / (2 * (j : ℝ) + 3) ^ 2) ≤ (17 / 72 : ℝ) - 1 / (4 * ((J : ℝ) + 2)) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [sum_range_succ]
    have ht := odd_term_bound ((J : ℝ) + 1) (by positivity)
    calc
      _ ≤ ((17 / 72 : ℝ) - 1 / (4 * ((J : ℝ) + 2))) +
          1 / (4 * (((J : ℝ) + 1) + 1) * (((J : ℝ) + 1) + 2)) := by
        exact add_le_add ih (by simpa only [Nat.cast_add, Nat.cast_one] using ht)
      _ = _ := by
        push_cast
        field_simp
        ring

theorem odd_uniform_sum (J : ℕ) : (∑ j ∈ range J, 1 / (2 * (j : ℝ) + 3) ^ 2) ≤ (17 / 72 : ℝ) := by
  cases J with
  | zero => norm_num
  | succ J =>
    exact (odd_partial_sum J).trans (sub_le_self _ (by positivity))

def modulus (j : ℕ) : ℕ := if j = 0 then 4 else (2 * j + 1) ^ 2

theorem modulus_positive (j : ℕ) : 0 < modulus j := by
  by_cases hj : j = 0
  · simp only [modulus, ite_eq_left hj]
    norm_num
  · simp only [modulus, ite_eq_right hj]
    positivity

theorem modulus_reciprocal_sum (J : ℕ) :
    (∑ j ∈ range (J + 1), 1 / (modulus j : ℝ)) ≤ (35 / 72 : ℝ) := by
  have hshift : ∀ j : ℕ, (modulus (j + 1) : ℝ) = (2 * (j : ℝ) + 3) ^ 2 := by
    intro j
    simp only [modulus, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_eq_right (show ¬False by simp)]
    push_cast
    ring
  rw [sum_range_succ']
  simp_rw [hshift]
  have hzero : (modulus 0 : ℝ) = 4 := rfl
  rw [hzero]
  have hh := odd_uniform_sum J
  linarith only [hh]

end PaperP1.AdjacentSquarefreeBudget
