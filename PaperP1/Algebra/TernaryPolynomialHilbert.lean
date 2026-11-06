module

public import PaperP1.Algebra.MvPolynomialHilbert
public import PaperP1.Algebra.GradedHilbertPolynomial
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Ring

/-! # The actual ternary polynomial grading has quadratic Hilbert coefficient one half -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPolynomialHilbert

open Polynomial

def polynomial : ℚ[X] := C (1 / 2 : ℚ) * X ^ 2 + C (3 / 2 : ℚ) * X + 1

theorem isHilbertPolynomial (F : Type*) [Field F] :
    GradedHilbertPolynomial.IsHilbertPolynomial (MvPolynomial.homogeneousSubmodule (Fin 3) F) polynomial := by
  refine ⟨0, fun n _hn ↦ ?_⟩
  rw [MvPolynomialHilbert.ternary_piece_finrank, Nat.cast_choose_two]
  simp only [polynomial, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem natDegree_le : polynomial.natDegree ≤ 2 := by unfold polynomial; compute_degree

theorem coeff_two : polynomial.coeff 2 = 1 / 2 := by simp [polynomial, Polynomial.coeff_one]

end PaperP1.TernaryPolynomialHilbert
