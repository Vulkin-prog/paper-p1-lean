module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Ring

/-! # The actual shifted difference of a quadratic Hilbert polynomial is linear with its exact coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticHilbertDifference

open Polynomial

theorem quadratic_evaluation (p : ℚ[X]) (hp : p.natDegree ≤ 2) (t : ℚ) :
    p.eval t = p.coeff 2 * t ^ 2 + p.coeff 1 * t + p.coeff 0 := by
  rw [Polynomial.eval_eq_sum_range' (n := 3) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, mul_one]
  ring

def difference (p : ℚ[X]) (e : ℕ) : ℚ[X] := p - p.comp (X - C (e : ℚ))

theorem expansion (p : ℚ[X]) (hp : p.natDegree ≤ 2) (e : ℕ) :
    difference p e = C (2 * (e : ℚ) * p.coeff 2) * X +
      C ((e : ℚ) * p.coeff 1 - (e : ℚ) ^ 2 * p.coeff 2) := by
  apply Polynomial.funext
  intro t
  simp only [difference, eval_sub, eval_comp, eval_X, eval_C, eval_add, eval_mul]
  rw [quadratic_evaluation p hp t, quadratic_evaluation p hp (t - (e : ℚ))]
  ring

theorem natDegree_le (p : ℚ[X]) (hp : p.natDegree ≤ 2) (e : ℕ) :
    (difference p e).natDegree ≤ 1 := by
  rw [expansion p hp e]
  compute_degree

theorem coefficient_one (p : ℚ[X]) (hp : p.natDegree ≤ 2) (e : ℕ) :
    (difference p e).coeff 1 = 2 * (e : ℚ) * p.coeff 2 := by
  rw [expansion p hp e]
  simp only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C_succ, mul_one, add_zero]

end PaperP1.QuadraticHilbertDifference
