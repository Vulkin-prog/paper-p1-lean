module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Ring

/-! # The rational quadratic polynomial for a finite homogeneous Veronese basis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedVeroneseHilbertPolynomial

open Polynomial

def term (D w : ℕ) : ℚ[X] :=
  C (1 / 2) * (C (D : ℚ) * X - C ((D * w : ℕ) : ℚ) + C 1) *
    (C (D : ℚ) * X - C ((D * w : ℕ) : ℚ) + C 2)

theorem term_expansion (D w : ℕ) :
    term D w = C ((D : ℚ) ^ 2 / 2) * X ^ 2 +
      C ((D : ℚ) * (3 - 2 * (D * w : ℕ)) / 2) * X +
      C ((((D * w : ℕ) : ℚ) ^ 2 - 3 * (D * w : ℕ) + 2) / 2) := by
  unfold term
  simp only [div_eq_mul_inv, Nat.cast_mul, map_mul, map_add, map_sub, map_pow, map_one, map_ofNat]
  ring

theorem term_eval (D w n : ℕ) (hw : w ≤ n) :
    (term D w).eval (n : ℚ) = (((n - w) * D + 2).choose 2 : ℚ) := by
  rw [term, Nat.cast_choose_two]
  simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub hw, Nat.cast_ofNat]
  ring

theorem term_natDegree_le (D w : ℕ) : (term D w).natDegree ≤ 2 := by
  rw [term_expansion]
  compute_degree

theorem term_coeff_two (D w : ℕ) : (term D w).coeff 2 = (D : ℚ) ^ 2 / 2 := by
  rw [term_expansion]
  simp

def polynomial {κ : Type*} [Fintype κ] (D : ℕ) (w : κ → ℕ) : ℚ[X] :=
  ∑ j : κ, term D (w j)

theorem polynomial_eval {κ : Type*} [Fintype κ] (D : ℕ) (w : κ → ℕ) (n : ℕ)
    (hw : ∀ j, w j ≤ n) :
    (polynomial D w).eval (n : ℚ) =
      ((∑ j : κ, ((n - w j) * D + 2).choose 2 : ℕ) : ℚ) := by
  simp only [polynomial, eval_finsetSum, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun j _ ↦ term_eval D (w j) n (hw j))

theorem polynomial_natDegree_le {κ : Type*} [Fintype κ] (D : ℕ) (w : κ → ℕ) :
    (polynomial D w).natDegree ≤ 2 := by
  apply natDegree_sum_le_of_forall_le
  exact fun j _ ↦ term_natDegree_le D (w j)

theorem polynomial_coeff_two {κ : Type*} [Fintype κ] (D : ℕ) (w : κ → ℕ) :
    (polynomial D w).coeff 2 = (Fintype.card κ : ℚ) * (D : ℚ) ^ 2 / 2 := by
  simp only [polynomial, finsetSum_coeff, term_coeff_two, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

end PaperP1.WeightedVeroneseHilbertPolynomial
