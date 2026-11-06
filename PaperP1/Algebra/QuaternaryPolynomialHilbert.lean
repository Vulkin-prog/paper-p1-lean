module

public import PaperP1.Algebra.MvPolynomialHilbert
public import PaperP1.Algebra.GradedHilbertPolynomial
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The exact actual cubic Hilbert polynomial of four ordinary homogeneous coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuaternaryPolynomialHilbert

open Polynomial

def polynomial : ℚ[X] := C (1 / 6 : ℚ) * X ^ 3 + X ^ 2 + C (11 / 6 : ℚ) * X + 1

theorem cast_choose_three (n : ℕ) : (((n + 3).choose 3 : ℕ) : ℚ) =
    ((n : ℚ) + 3) * ((n : ℚ) + 2) * ((n : ℚ) + 1) / 6 := by
  have hh := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_succ_right_eq (n + 3) 2)
  have he : n + 3 - 2 = n + 1 := by omega
  rw [he] at hh
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.cast_choose_two] at hh
  nlinarith [hh]

theorem isHilbertPolynomial (F : Type*) [Field F] :
    GradedHilbertPolynomial.IsHilbertPolynomial (MvPolynomial.homogeneousSubmodule (Fin 4) F) polynomial := by
  refine ⟨0, fun n _hn ↦ ?_⟩
  rw [MvPolynomialHilbert.piece_finrank, Nat.card_fin, show 4 + n - 1 = n + 3 by omega,
    Nat.choose_symm_add, cast_choose_three]
  simp only [polynomial, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one]
  ring

theorem natDegree_le : polynomial.natDegree ≤ 3 := by unfold polynomial; compute_degree

theorem coeff_three : polynomial.coeff 3 = 1 / 6 := by simp [polynomial, Polynomial.coeff_one]

end PaperP1.QuaternaryPolynomialHilbert
